-- Prove2me | Theorems.Thm_PositivityTheory_KReal_low_rai
-- name    : PositivityTheory.KReal.low_rai
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:54.983641+00:00
-- url     : https://prove2.me/theorems/66881736-1a4d-43ae-a08d-c9177e307eea
-- title:
--   KReal: low rai
-- statement:
--   The KReal construction uses the low rai property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/FockAct1FockAct2Commute.lean#L132-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/FockAct1FockAct2Commute.lean#L132-L144

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

theorem PositivityTheory.KReal.low_rai (a b : Ln p q r s) :
    lowB a * raiB b = raiB b * lowB a + if a = b then 1 else 0 := by sorry
