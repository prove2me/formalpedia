-- Prove2me | Theorems.Thm_TarskiBootstrap_Dimensional_Supplement_lemma_2_11
-- name    : TarskiBootstrap.Dimensional.Supplement.lemma_2_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:05:29.168709+00:00
-- url     : https://prove2.me/theorems/4c5f66d8-e85c-47eb-b46f-c2d1c706ef49
-- title:
--   Lemma 2.11 — Adversary reduction lemma
-- statement:
--   Let $\Sigma_1,\Pi_1,\Sigma_2,\Pi_2$ be finite alphabets and $I_1,I_2$ finite index sets, and let $\Phi_1$, $\Phi_2$ be functions on query strings $f:I_1\to\Sigma_1$ and $g:I_2\to\Sigma_2$. Let $\mathcal F_1$ be a set of strings and $\Gamma$ a nonnegative adversary matrix for $\Phi_1|_{\mathcal F_1}$ yielding a spectral lower bound of $\lambda/\delta$ with $\delta>0$, that is $\|\Gamma\|\ge\lambda$ and $\|\Gamma\circ\Delta^{(1)}_i\|\le\delta$ for every $i\in I_1$. Let $\iota:\mathcal F_1\to\Sigma_2^{I_2}$ satisfy:
--
--   1. (2.15) for all $f_1,f_2\in\mathcal F_1$, $\Phi_2(\iota(f_1))=\Phi_2(\iota(f_2))\Rightarrow\Phi_1(f_1)=\Phi_1(f_2)$;
--   2. (2.16) for a positive integer $c$ and maps $q_1,\dots,q_c:I_2\to I_1$, for every $z\in I_2$ and $f_1,f_2\in\mathcal F_1$,
--   $$
--   \iota(f_1)(z)\ne\iota(f_2)(z)\ \Longrightarrow\ \exists j\in\{1,\dots,c\},\ f_1(q_j(z))\ne f_2(q_j(z)).
--   $$
--
--   Then, with $\mathcal F_2=\iota(\mathcal F_1)$, there is a nonnegative adversary matrix $\Gamma'$ for $\Phi_2|_{\mathcal F_2}$ with
--
--   $$
--   \|\Gamma'\|\ge\lambda\qquad\text{and}\qquad \max_{z\in I_2}\|\Gamma'\circ\Delta^{(2)}_z\|\le c\,\delta,
--   $$
--
--   i.e. a spectral lower bound of $\lambda/(c\delta)$. Norms are spectral norms.
--
--   This lemma transfers an adversary bound through an embedding whose queries are local, losing only the factor $c$; it is the last step of the proofs of Theorems 1.2 and 1.3, both with $c=2$.
--
--   Differences from the source:
--   - encoding: partial functions Φ_i : S_i → Π_i with S_i ⊆ Σ_i^{I_i}, F_1 ⊆ S_1 and ι : F_1 → S_2 → total functions Φ_i on Σ_i^{I_i}, F_1 any set of strings and ι : F_1 → Σ_2^{I_2}; reason: only the values of Φ_1 on F_1 and of Φ_2 on ι(F_1) enter; every partial instance extends to a total one
--   - encoding: maps q_1, …, q_c and ∃ j ∈ {1, …, c} → q : Fin c → I_2 → I_1 and ∃ j : Fin c; reason: reindexing
-- source:
--   Li, Ma, Yang and Zhao, Bootstrapping Classical and Quantum Query Lower Bounds for Finding Tarski Fixed Points, STOC 2027 submission #6 (2026), frozen preprint, Lemma 2.11, PDF/printed pp. 9–10, SHA-256 320afa8333f95589a388b30ffbfd6d7b7e5d93cdf07fa8630825fbf7d0107d59; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/6.pdf. Printed page = PDF page. No arXiv identifier/version supplied.

import Definitions.Def_TarskiBootstrap_Dimensional_Witness

open scoped Matrix

namespace TarskiBootstrap.Dimensional.Supplement

open scoped Classical

/-- Lemma 2.11 (Adversary Reduction Lemma), PDF/printed pp. 9–10. Inputs are query
strings `I₁ → Σ₁`, `I₂ → Σ₂` over finite index sets and alphabets; `Φ₁`, `Φ₂` are given
as total functions, of which only the values on `F₁` and `ι(F₁)` matter. The
distinguisher of the new problem at `z` compares `ι(f)(z)`. -/
theorem lemma_2_11 {I₁ I₂ Sig₁ Sig₂ Out₁ Out₂ : Type*}
    [Fintype I₁] [Fintype I₂] [Fintype Sig₁] [Fintype Sig₂]
    [Fintype Out₁] [Fintype Out₂]
    (Φ₁ : (I₁ → Sig₁) → Out₁) (Φ₂ : (I₂ → Sig₂) → Out₂)
    (F₁ : Set (I₁ → Sig₁)) (lam δ : ℝ) (hδ : 0 < δ)
    (Γ : Matrix F₁ F₁ ℝ)
    (hΓ : NonnegativeAdversary (fun f : F₁ => Φ₁ f.val) Γ)
    (hw : SpectralWitness (fun f : F₁ => f.val) Γ lam δ)
    (ι : F₁ → (I₂ → Sig₂))
    (h_out : ∀ f₁ f₂ : F₁, Φ₂ (ι f₁) = Φ₂ (ι f₂) → Φ₁ f₁.val = Φ₁ f₂.val)
    (c : ℕ) (hc : 0 < c) (q : Fin c → I₂ → I₁)
    (h_query : ∀ z : I₂, ∀ f₁ f₂ : F₁, ι f₁ z ≠ ι f₂ z →
      ∃ j : Fin c, f₁.val (q j z) ≠ f₂.val (q j z)) :
    ∃ Γ' : Matrix (Set.range ι) (Set.range ι) ℝ,
      NonnegativeAdversary (fun g : Set.range ι => Φ₂ g.val) Γ' ∧
      SpectralWitness (fun g : Set.range ι => g.val) Γ' lam ((c : ℝ) * δ) := by sorry

end TarskiBootstrap.Dimensional.Supplement
