-- Prove2me | Theorems.Thm_SliceLinearity_Tests_lemma_6_9
-- name    : SliceLinearity.Tests.lemma_6_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T02:38:32.982849+00:00
-- url     : https://prove2.me/theorems/7b513941-e4a6-45d6-b9fb-41b68146a58e
-- title:
--   Lemma 6.9 — a [−1,1]-valued model depending on d ≤ ε⁻² characters, ignoring n/2^d coordinates, with ‖ĝ‖_{ℓ1} ≤ 2^{d/2}
-- statement:
--   Let $\nu$ be supported on $H_{\rm even}$, and let $f$ be real with $|f|\le1$. For every $\varepsilon>0$ there is a function $g:\mathbb F_2^n\to[-1,1]$ depending on $d\le\varepsilon^{-2}$ characters and ignoring at least $n/2^d$ coordinates, with
--   $$\max_\chi|\langle f-g,\chi\rangle_\nu|\le\varepsilon,\qquad\|\hat g\|_{\ell_1}\le2^{d/2}.$$
--
--   Differences from the source:
--   - encoding: "depending on d characters", "ignoring at least n/2^d coordinates" → g = H(χ_{ξ₁}, …, χ_{ξ_d}) for some H : (Fin d → ℝ) → ℝ; a set B with n/2^d ≤ |B| that g ignores; reason: direct transcriptions
--   - encoding: ν supported on H_even → a distribution ν with ν x ≠ 0 → x ∈ H_even; reason: same objects
-- source:
--   Aydin, Larsen, Mittal, Richelson, Roy, Low Soundness Linearity Testing on Subsets of the Hypercube, STOC 2027 submission (manuscript sha256 457be236…), §6.2, p. 44 (PDF 46), Lemma 6.9

import Mathlib
import Definitions.Def_SliceLinearity_Tests_BiasedAnalysis

set_option autoImplicit false

namespace SliceLinearity.Tests

/-- **Lemma 6.9** (Regularity by characters), p. 44 (PDF 46). Let `ν` be a distribution supported on
`H_even`, and let `f` be real with `|f| ≤ 1`. For every `ε > 0` there is `g : F₂ⁿ → [−1, 1]` depending on
`d ≤ ε^{−2}` characters (`g = H(χ_{ξ₁}, …, χ_{ξ_d})`) and ignoring a set `B` of at least `n/2^d`
coordinates, with `max_χ |⟨f − g, χ⟩_ν| ≤ ε` and `‖ĝ‖_{ℓ1} ≤ 2^{d/2}`. -/
theorem lemma_6_9 {n : ℕ} (ν : Cube n → ℝ) (hν : IsDistW ν)
    (hsupp : ∀ x, ν x ≠ 0 → x ∈ evenCube n) (f : Cube n → ℝ) (hf : ∀ x, |f x| ≤ 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (g : Cube n → ℝ) (d : ℕ) (ξ : Fin d → Cube n) (H : (Fin d → ℝ) → ℝ) (B : Finset (Fin n)),
      (∀ x, |g x| ≤ 1) ∧ (∀ x, g x = H fun j => chi (ξ j) x) ∧ (d : ℝ) ≤ ε ^ (-2 : ℤ) ∧
      (n : ℝ) / (2 : ℝ) ^ d ≤ (B.card : ℝ) ∧ IgnoresCoords g B ∧
      maxCorr ν (fun x => f x - g x) ≤ ε ∧ fourierL1 g ≤ (2 : ℝ) ^ ((d : ℝ) / 2) := by sorry

end SliceLinearity.Tests
