-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFPB_Kf_contDiff
-- name    : PositivityTheory.SiegelWeilFormula.KFPB.Kf_contDiff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:22:41.301304+00:00
-- url     : https://prove2.me/theorems/09d479f5-66a4-4907-b686-447b32814788
-- title:
--   KFPB: Kf cont Diff
-- statement:
--   The KFPB construction uses the Kf cont Diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/PolynomialGaussianIntegrals/PolyGaussOfLines.lean#L48-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/PolynomialGaussianIntegrals/PolyGaussOfLines.lean#L48-L54

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

theorem PositivityTheory.SiegelWeilFormula.KFPB.Kf_contDiff {c : ℝ} (hc : 0 ≤ c) (h : 𝓢(EuclideanSpace ℝ ι, ℂ)) (N : ℕ) : ContDiff ℝ N (Kf c h) := by sorry
