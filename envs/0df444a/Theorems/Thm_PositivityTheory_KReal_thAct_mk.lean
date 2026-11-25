-- Prove2me | Theorems.Thm_PositivityTheory_KReal_thAct_mk
-- name    : PositivityTheory.KReal.thAct_mk
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:16:21.866635+00:00
-- url     : https://prove2.me/theorems/31771700-8a7f-5027-9521-49d7902c67bf
-- title:
--   KReal: th Act mk
-- statement:
--   The KReal construction uses the th Act mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreDefs.lean#L115-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreDefs.lean#L115-L118

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

theorem PositivityTheory.KReal.thAct_mk (p q r s : ℕ) (c τ : ℂ) (W : Mat r s) (f : Pol p q r s) :
    thAct p q r s c τ W (thMkC p q r s c f) = thMkC p q r s c (twAct p q r s τ W f) := by sorry
