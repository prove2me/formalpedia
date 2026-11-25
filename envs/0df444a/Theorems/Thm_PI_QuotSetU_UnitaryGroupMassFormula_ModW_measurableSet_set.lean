-- Prove2me | Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_ModW_measurableSet_set
-- name    : PI.QuotSetU.UnitaryGroupMassFormula.ModW.measurableSet_set
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:18:27.777796+00:00
-- url     : https://prove2.me/theorems/b5742d85-5aac-4de9-ab51-4e972def34f8
-- title:
--   Mod W: measurable Set set
-- statement:
--   The Mod W construction uses the measurable Set set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/ModBase.lean#L82-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/ModBase.lean#L82-L83

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SsetGroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_ModBase
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Topology
open scoped ENNReal NNReal
noncomputable section
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.ModW
open PI
variable {m : ℕ}
variable {G : Set (Matrix (Fin m) (Fin m) ℂ)} {hG : IsMatGroup G}
open MG

theorem PI.QuotSetU.UnitaryGroupMassFormula.ModW.measurableSet_set (hG : IsMatGroup G) : MeasurableSet {x : MtM m | Matrix.of x ∈ G} := by sorry
