-- Prove2me | Theorems.Thm_TarskiBootstrap_Dimensional_Supplement_lemma_4_9
-- name    : TarskiBootstrap.Dimensional.Supplement.lemma_4_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:08:30.228194+00:00
-- url     : https://prove2.me/theorems/c07e2f94-065e-4f5a-82ab-42bd9f05a19e
-- title:
--   Lemma 4.9 — Properties of the staircase constructor
-- statement:
--   Let $\mathcal F$, $A$ be as in Lemma 4.3 and $m\ge2$. An element $(s,f)$ of the composite domain $\mathcal D$ consists of an ordered search instance $s=(s_1,\dots,s_m)$ with hidden position $i_0$ ($s_r=1$ for $r<i_0$, $s_{i_0}=0$, $s_r=-1$ for $r>i_0$) and $f=(f_1,\dots,f_m)\in\mathcal F^m$. For the staircase constructor $\hat{\mathcal E}$:
--
--   1. for every $(s,f)\in\mathcal D$, $\hat{\mathcal E}(s,f):S\to S$ is monotone;
--   2. for every $(s,f)\in\mathcal D$, the unique fixed point of $\hat{\mathcal E}(s,f)$ is $((i_0,f_{i_0}^*),(i_0,f_{i_0}^*))$, where $s_{i_0}=0$;
--   3. for any $(s^{(1)},f^{(1)}),(s^{(2)},f^{(2)})\in\mathcal D$ and any $u=((i,x),(j,y))\in S$, with $q_1(u)=(i,x)$, $q_2(u)=(j,y)$ and $h^{(a)}(r,z)=H_{s^{(a)}_r}(f^{(a)}_r)(z)$,
--   $$
--   \hat{\mathcal E}(s^{(1)},f^{(1)})(u)\ne\hat{\mathcal E}(s^{(2)},f^{(2)})(u)\ \Longrightarrow\ \exists\ell\in\{1,2\},\ h^{(1)}(q_\ell(u))\ne h^{(2)}(q_\ell(u)).
--   $$
--
--   These properties make the embedded family a valid Tarski family with unique fixed points and give the locality constant $c=2$ for the adversary reduction lemma.
--
--   Differences from the source:
--   - encoding: a hard instance family for Tarski(n, k) in which every function has a unique fixed point → F : Set (Grid n k → Grid n k) with every member monotone and having a unique fixed point; reason: Definition 2.1: instances are monotone self-maps of [n]^k; "hard" adds no assumption beyond the stated witness
--   - encoding: all possible fixed points lie on an antichain A → A antichain with possibleAnswers F ⊆ A; reason: literal transcription; the set of possible fixed points is the published possibleAnswers F
--   - encoding: an integer m ≥ 2 → m : ℕ+ with 2 ≤ m; reason: same values
--   - encoding: positions and block indices 1, …, m → Fin m = {0, …, m-1}; reason: order-preserving reindexing
--   - encoding: (s, f) ∈ D → labels (i₀, f) with s = osInstance m i₀ and f : Fin m → F; reason: by (2.13) and the labelling of F′, D consists exactly of the oracles of such pairs, and block r has inner answer s_r
--   - encoding: Q with the lexicographic order, S ⊆ Q² with the induced product order, Ê(s, f) : S → S → Fin m ×ₗ Grid n k, a subtype of Q × Q, and a map of that subtype; reason: Mathlib’s lexicographic product has exactly the order of (4.8)
--   - encoding: ∃ ℓ ∈ {1, 2} → a disjunction of the two cases; reason: two-element existential
-- source:
--   Li, Ma, Yang and Zhao, Bootstrapping Classical and Quantum Query Lower Bounds for Finding Tarski Fixed Points, STOC 2027 submission #6 (2026), frozen preprint, Lemma 4.9, PDF/printed pp. 21–22, SHA-256 320afa8333f95589a388b30ffbfd6d7b7e5d93cdf07fa8630825fbf7d0107d59; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/6.pdf. Printed page = PDF page. No arXiv identifier/version supplied.

import Definitions.Def_TarskiBootstrap_Dimensional_Supplement_Staircase
import Definitions.Def_TarskiBootstrap_Dimensional_Supplement_Composite

namespace TarskiBootstrap.Dimensional.Supplement

/-- Lemma 4.9, PDF/printed pp. 21–22. An element `(s, f)` of the composite domain `D`
is labelled by its hidden position `i₀` (so `s = osInstance m i₀`) and `f ∈ F^m`.
(1) `Ê(s, f)` is monotone on the staircase `S`; (2) its unique fixed point is
`((i₀, f_{i₀}*), (i₀, f_{i₀}*))`, where `s_{i₀} = 0`; (3) with `q₁(u) = (i, x)`,
`q₂(u) = (j, y)` for `u = ((i, x), (j, y)) ∈ S`, a difference of the two staircase values
at `u` forces a difference of the composite oracles `h(r, z) = H_{s_r}(f_r)(z)` at
`q₁(u)` or `q₂(u)`. -/
theorem lemma_4_9 {n k : ℕ+} (F : Set (Grid n k → Grid n k)) (A : Set (Grid n k))
    (hF : ∀ f : F, Monotone f.val ∧ ∃! x, f.val x = x)
    (hA : IsAntichain (· ≤ ·) A) (hcontains : possibleAnswers F ⊆ A)
    (m : ℕ+) (hm : 2 ≤ (m : ℕ)) :
    (∀ (i₀ : Fin (m : ℕ)) (f : Fin (m : ℕ) → F),
      Monotone (staircase A (osInstance m i₀) (fun r => (f r).val))) ∧
    (∀ (i₀ : Fin (m : ℕ)) (f : Fin (m : ℕ) → F) (u : Staircase n k m),
      staircase A (osInstance m i₀) (fun r => (f r).val) u = u ↔
        u.val = (toLex (i₀, fixedPoint (f i₀).val), toLex (i₀, fixedPoint (f i₀).val))) ∧
    (∀ (i₁ i₂ : Fin (m : ℕ)) (f₁ f₂ : Fin (m : ℕ) → F) (u : Staircase n k m),
      staircase A (osInstance m i₁) (fun r => (f₁ r).val) u ≠
          staircase A (osInstance m i₂) (fun r => (f₂ r).val) u →
        compositeOracle A (osInstance m i₁) (fun r => (f₁ r).val) (ofLex u.val.1) ≠
            compositeOracle A (osInstance m i₂) (fun r => (f₂ r).val) (ofLex u.val.1) ∨
          compositeOracle A (osInstance m i₁) (fun r => (f₁ r).val) (ofLex u.val.2) ≠
            compositeOracle A (osInstance m i₂) (fun r => (f₂ r).val) (ofLex u.val.2)) := by sorry

end TarskiBootstrap.Dimensional.Supplement
