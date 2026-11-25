-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_KLI_integrable_gaussian_moment
-- name    : PositivityTheory.SiegelWeilFormula.KLI.integrable_gaussian_moment
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:50:10.386516+00:00
-- url     : https://prove2.me/theorems/f1677afd-c868-4250-8c44-e7af03e47687
-- title:
--   KLI: integrable gaussian moment
-- statement:
--   The KLI construction uses the integrable gaussian moment property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/LocalOperatorBlocks/GaussianMomentRealCoords.lean#L62-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/LocalOperatorBlocks/GaussianMomentRealCoords.lean#L62-L77

import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_LocalOperatorBlocks_EvalMonomial2
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_LocalOperatorBlocks_GaussianMomentRealCoords
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex MvPolynomial
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KLI

theorem PositivityTheory.SiegelWeilFormula.KLI.integrable_gaussian_moment (sg : ℤˣ) (t z ξ : ℂ) (hz : 0 < ((sg : ℤ) : ℝ) * z.im) (α β : ℕ) :
    Integrable (phi1 sg t z ξ α β) := by sorry
