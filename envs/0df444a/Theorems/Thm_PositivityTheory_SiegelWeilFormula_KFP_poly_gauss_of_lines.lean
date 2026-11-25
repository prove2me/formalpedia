-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFP_poly_gauss_of_lines
-- name    : PositivityTheory.SiegelWeilFormula.KFP.poly_gauss_of_lines
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:58:20.60739+00:00
-- url     : https://prove2.me/theorems/b44a9c22-d6a2-4b7c-9e48-cc82f1651416
-- title:
--   KFP: poly gauss of lines
-- statement:
--   The KFP construction uses the poly gauss of lines property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/RealAdelicFockSpace/PolyGaussOfLines.lean#L19-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/RealAdelicFockSpace/PolyGaussOfLines.lean#L19-L25

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_PolynomialGaussianIntegrals_IteratedDerivScale
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_PolynomialGaussianIntegrals_IntegrableRexpLin
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_PolynomialGaussianIntegrals_PolyGaussOfLines
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_RealAdelicFockSpace_PolyGaussOfLines
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFPB_poly_gauss_of_lines

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KFP

theorem PositivityTheory.SiegelWeilFormula.KFP.poly_gauss_of_lines {ι : Type} [Fintype ι] (c : ℝ) (hc : 0 < c) (N : ℕ) (h : 𝓢(EuclideanSpace ℝ ι, ℂ))
    (H : ∀ ξ : EuclideanSpace ℝ ι, ∃ p : Polynomial ℂ, p.natDegree ≤ N ∧ ∀ z : ℂ,
      ∫ u, h u * Real.exp (-(c * ‖u‖ ^ 2)) * Complex.exp (z * ⟪ξ, u⟫_ℝ) =
        Complex.exp (z ^ 2 * ‖ξ‖ ^ 2 / (8 * c)) * p.eval z) :
    ∃ P : MvPolynomial ι ℂ, P.totalDegree ≤ N ∧
      ∀ u, h u = MvPolynomial.eval (fun i => ((u i : ℝ) : ℂ)) P * Real.exp (-(c * ‖u‖ ^ 2)) := by sorry
