-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFPB_multi_poly
-- name    : PositivityTheory.SiegelWeilFormula.KFPB.multi_poly
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:50:06.524674+00:00
-- url     : https://prove2.me/theorems/ec550ab6-7d42-42ff-b182-7136e106c412
-- title:
--   KFPB: multi poly
-- statement:
--   The KFPB construction uses the multi poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/PolynomialGaussianIntegrals/IteratedDerivPolyRealZero.lean#L50-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/PolynomialGaussianIntegrals/IteratedDerivPolyRealZero.lean#L50-L69

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_PolynomialGaussianIntegrals_IteratedDerivPolyRealZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KFPB
variable {ι : Type} [Fintype ι]

theorem PositivityTheory.SiegelWeilFormula.KFPB.multi_poly (k : ℕ) (M : ContinuousMultilinearMap ℝ (fun _ : Fin k => EuclideanSpace ℝ ι) ℂ) :
    ∃ Q : MvPolynomial ι ℂ, Q.totalDegree ≤ k ∧
      ∀ η : EuclideanSpace ℝ ι, M (fun _ => η) = MvPolynomial.eval (fun i => ((η i : ℝ) : ℂ)) Q := by sorry
