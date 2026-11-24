-- Prove2me | Theorems.Thm_PositivityTheory_KReal_low_low
-- name    : PositivityTheory.KReal.low_low
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:52.803775+00:00
-- url     : https://prove2.me/theorems/6fd9819f-8b54-484a-bcf1-925187a3893d
-- title:
--   KReal: low low
-- statement:
--   The KReal construction uses the low low property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/FockAct1FockAct2Commute.lean#L122-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/FockAct1FockAct2Commute.lean#L122-L130

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_JointBlockShapes_JointShape
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_FockAct1FockAct2Commute
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial FockH1Action
open PositivityTheory PositivityTheory.KReal
variable {p q r s : ℕ}

theorem PositivityTheory.KReal.low_low (a b : Ln p q r s) : lowB a * lowB b = lowB b * lowB a := by sorry
