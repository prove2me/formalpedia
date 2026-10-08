-- Prove2me | Theorems.Thm_PCSPBLPAff_Characterization_lemma_9_finite_subset_hom
-- name    : PCSPBLPAff.Characterization.lemma_9_finite_subset_hom
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:08:16.24402+00:00
-- url     : https://prove2.me/theorems/a9c42a00-d20d-4f13-841c-6d8607ea2c1c
-- title:
--   Proof of Lemma 9, p. 11 — a symmetric polymorphism of arity L* ≥ Mℓ² gives a minion homomorphism on the finite subset M_{ℓ,M}
-- statement:
--   Fix $\ell,M\in\mathbb N$ with $\ell\ge1$, and let $\mathcal M_{\ell,M}$ be the set of objects $(w,r)$ of $\mathcal M_{\mathrm{BLP+Aff}}$ (of any arity $L$) such that $\ell w(i)\in\mathbb Z$ for all $i$ and $\sum_i|r(i)|\le M$. Let $f:A^{L^*}\to B$ be a symmetric polymorphism of $(\mathbf A,\mathbf B)$ of arity $L^*\ge M\ell^2$, and write $L^*=u\ell+v$ with $u,v\in\mathbb N$ and $v\in\{0,\dots,\ell-1\}$.
--
--   Then there is a map $\xi$ from objects of $\mathcal M_{\mathrm{BLP+Aff}}$ to functions of the same arity such that for every $(w,r)\in\mathcal M_{\ell,M}$ of arity $L$:
--
--   1. $\xi(w,r)$ is the $L$-ary minor $f_{/\sigma}$ of $f$ along some $\sigma:[L^*]\to[L]$ in which coordinate $i$ is repeated exactly
--   $$W_i=u\ell\,w(i)+v\,r(i)$$
--   times, i.e. $|\sigma^{-1}(i)|=W_i$ for all $i\in[L]$;
--   2. $\xi$ preserves minors on $\mathcal M_{\ell,M}$: $\xi((w,r)_{/\pi})=\xi(w,r)_{/\pi}$ for every $\pi:[L]\to[L']$.
--
--   This is the one-block construction in the proof of Lemma 9: for fixed $\ell,M$ it gives a minion homomorphism from $\mathcal M_{\ell,M}$ into the subminion of minors of $f$. A compactness argument over $\ell$ and $M$ then yields Lemma 9.
--
--   **Formalization Note** The map $\xi$ is constrained only on $\mathcal M_{\ell,M}$. The hypothesis $\ell\ge1$ is implied by $v<\ell$ and is stated for readability. The repetition counts are compared in $\mathbb Q$.
-- source:
--   arXiv:1907.04383v3, proof of Lemma 9, p. 11, paragraphs "We define finite subsets" to "We claim that this map is a minion homomorphism"

import Mathlib
import Definitions.Def_PCSPBLPAff_Characterization_Setting

namespace PCSPBLPAff.Characterization

/-- Proof of Lemma 9, p. 11 (one block): fix `ℓ ≥ 1` and `M`, and a symmetric polymorphism `f`
of arity `L* ≥ Mℓ²`, with `L* = uℓ + v`, `0 ≤ v < ℓ`. There is a map `ξ` which, on the
finite subset `M_{ℓ,M}` of objects `(w, r)` with `ℓ w(i) ∈ ℤ` and `∑ |r(i)| ≤ M`, sends
`(w, r)` of arity `L` to the `L`-ary minor `f_{/σ}` of `f` in which `x_i` is repeated
`W_i = uℓ w(i) + v r(i)` times, and which preserves minors on `M_{ℓ,M}`. -/
theorem lemma_9_finite_subset_hom {τ : Type} {ar : τ → ℕ} {A B : Type}
    (𝔸 : PCSPBLPAff.Symmetric.RelStruct τ ar A) (𝔹 : PCSPBLPAff.Symmetric.RelStruct τ ar B)
    (ℓ M Lstar u v : ℕ) (hℓ : 0 < ℓ) (hLstar : M * ℓ ^ 2 ≤ Lstar)
    (huv : Lstar = u * ℓ + v) (hv : v < ℓ)
    (f : (Fin Lstar → A) → B) (hf : PCSPBLPAff.Symmetric.IsPolymorphism 𝔸 𝔹 f) (hsym : PCSPBLPAff.Symmetric.IsSymmetric f) :
    ∃ ξ : (L : ℕ) → BLPAffObj (Fin L) → (Fin L → A) → B,
      ∀ (L : ℕ) (x : BLPAffObj (Fin L)),
        (∀ i, ∃ z : ℤ, (ℓ : ℚ) * x.1.1 i = z) → ∑ i, |x.1.2 i| ≤ (M : ℤ) →
          (∃ σ : Fin Lstar → Fin L,
              (∀ i, (((Finset.univ.filter (fun l => σ l = i)).card : ℕ) : ℚ) =
                (u : ℚ) * ℓ * x.1.1 i + (v : ℚ) * (x.1.2 i : ℚ)) ∧
              ξ L x = polMinor σ f) ∧
          ∀ (L' : ℕ) (π : Fin L → Fin L') (h : IsBLPAffObj (minorQ π x.1.1) (minorZ π x.1.2)),
            ξ L' ⟨(minorQ π x.1.1, minorZ π x.1.2), h⟩ = polMinor π (ξ L x) := by sorry

end PCSPBLPAff.Characterization
