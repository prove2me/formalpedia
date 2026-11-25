-- Prove2me | Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_finite_compact_measure
-- name    : PI.NMeasInv.UnitaryGroupMassFormula.finite_compact_measure
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:15:13.160631+00:00
-- url     : https://prove2.me/theorems/592bcc54-26ec-4740-a70a-6b326484c448
-- title:
--   Unitary Group Mass Formula: finite compact measure
-- statement:
--   The Unitary Group Mass Formula construction uses the finite compact measure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureInverseContraction/Development.lean#L27-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureInverseContraction/Development.lean#L27-L30

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_NMeasInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_RightInvOfContract
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_ContinuousUMatApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_HaarSub
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_ModOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstLeftInvMuInf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstAll
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_Development
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory NumberField
open PI PI.NMeasInv PI.NMeasInv.UnitaryGroupMassFormula

theorem PI.NMeasInv.UnitaryGroupMassFormula.finite_compact_measure : FinCpt := by sorry
