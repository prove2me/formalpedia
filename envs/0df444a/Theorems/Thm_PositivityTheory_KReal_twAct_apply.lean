-- Prove2me | Theorems.Thm_PositivityTheory_KReal_twAct_apply
-- name    : PositivityTheory.KReal.twAct_apply
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:16:11.876889+00:00
-- url     : https://prove2.me/theorems/c154c967-4d8c-5383-ae65-a760e5651241
-- title:
--   KReal: tw Act apply
-- statement:
--   The KReal construction uses the tw Act apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreDefs.lean#L92-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreDefs.lean#L92-L94

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_TensorIrr
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_FockHarmSplit
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_FockJointMult
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_FockOneDeg
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_FockWtDeg
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_FockRaiseLow
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action
open scoped InnerProductSpace
open PositivityTheory PositivityTheory.KReal

theorem PositivityTheory.KReal.twAct_apply (p q r s : ℕ) (τ : ℂ) (W : Mat r s) (f : Pol p q r s) :
    twAct p q r s τ W f = fockAct2 p q r s W f + (τ * W.trace) • f := by sorry
