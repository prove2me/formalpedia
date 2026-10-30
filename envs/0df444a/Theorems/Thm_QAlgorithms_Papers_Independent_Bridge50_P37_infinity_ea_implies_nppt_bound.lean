-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P37_infinity_ea_implies_nppt_bound
-- name    : QAlgorithms.Papers.Independent.Bridge50.P37.infinity_ea_implies_nppt_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:43:32.540981+00:00
-- url     : https://prove2.me/theorems/867d3457-7421-48b8-8f80-72b51444b9c2
-- title:
--   Unnumbered consequence: infinite local annihilation implies NPPT bound entanglement
-- statement:
--   Write $M_d$ for complex $d\times d$ matrices in fixed orthonormal bases; positive means positive semidefinite. All maps are complex-linear and all dimensions are positive integers.
--
--   If a finite-dimensional channel $T$ is infinitely locally entanglement annihilating and is not entanglement breaking, then
--   $$\exists d\ge2,\quad\exists\rho\in M_d\otimes M_d:\quad\rho\text{ is NPPT bound entangled}.$$
--   The input of every tensor power of $T$ is arbitrary and its entire output must be fully separable. This is a conditional consequence of Theorems 5 and 4, not an unconditional construction of such a channel.
-- source:
--   Positivity of linear maps under tensor powers, arXiv:1502.05630v2, PDF p. 8, Unnumbered consequence: infinite local annihilation implies NPPT bound entanglement

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P37

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

-- Only the following exact definition bodies are reused from pinned accepted papers.

open QAlgorithms.Papers.Independent.Information100.P04 (gamma copies)

open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap IsPositiveMap)

open QAlgorithms.Papers.Independent.Information100.P50 (maxEigenvalue)

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Information100.P69 (diamond)

open QAlgorithms.Papers.Independent.Information100.P56 (normalizedChoi)

open QAlgorithms.Papers.Independent.Information100.P76 (swapMatrix)

open QAlgorithms.Papers.Independent.Next46.P39 (inverseSqrt)

namespace QAlgorithms.Papers.Independent.Bridge50.P37

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

/-- Explicit unnumbered consequence opening PDF p.8: conditional existence only. -/
theorem infinity_ea_implies_nppt_bound [Nonempty A] [Nonempty B] (T : MatrixMap A B)
    (hT : IsChannel T) (hEA : InfinityEA T) (hEB : ¬ RectangularEBPositive T) :
    ∃ d : ℕ, 2 ≤ d ∧ ∃ X : Mat (Fin d × Fin d), NPPTBound X := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P37

end
