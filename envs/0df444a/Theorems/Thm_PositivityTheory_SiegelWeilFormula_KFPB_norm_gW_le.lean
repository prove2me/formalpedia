-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFPB_norm_gW_le
-- name    : PositivityTheory.SiegelWeilFormula.KFPB.norm_gW_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:22:02.921312+00:00
-- url     : https://prove2.me/theorems/fd65d7e6-3c77-5b77-b1fd-99939401ea42
-- title:
--   KFPB: norm g W le
-- statement:
--   The KFPB construction uses the norm g W le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/PolynomialGaussianIntegrals/PolyGaussOfLines.lean#L19-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/PolynomialGaussianIntegrals/PolyGaussOfLines.lean#L19-L24

import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_PolynomialGaussianIntegrals_IteratedDerivPolyRealZero
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_PolynomialGaussianIntegrals_IntegrablePolyGauss
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_PolynomialGaussianIntegrals_PolyGaussOfLines
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped SchwartzMap InnerProductSpace FourierTransform
open MeasureTheory
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KFPB
variable {ι : Type} [Fintype ι]

theorem PositivityTheory.SiegelWeilFormula.KFPB.norm_gW_le {c : ℝ} (hc : 0 ≤ c) (h : EuclideanSpace ℝ ι → ℂ) (u : EuclideanSpace ℝ ι) :
    ‖gW c h u‖ ≤ ‖h u‖ := by sorry
