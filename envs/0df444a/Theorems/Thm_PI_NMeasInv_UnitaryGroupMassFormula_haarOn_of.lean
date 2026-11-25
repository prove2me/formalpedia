-- Prove2me | Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_haarOn_of
-- name    : PI.NMeasInv.UnitaryGroupMassFormula.haarOn_of
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T06:14:08.131734+00:00
-- url     : https://prove2.me/theorems/fbbf7f77-4fa5-5997-b600-975b97e31c4c
-- title:
--   Unitary Group Mass Formula: haar On of
-- statement:
--   The Unitary Group Mass Formula construction uses the haar On of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureInverseContraction/Development.lean#L22-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureInverseContraction/Development.lean#L22-L25

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

theorem PI.NMeasInv.UnitaryGroupMassFormula.haarOn_of (I : Formalism.MainNotions.S.AutInst) {r : ℕ} (e : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E)
    (μ : Measure I.Ginf) (hμ : IsHaarOnSet I (Ninf I e z) μ) :
    HaarOn (PI.ScMuExists.UnitaryGroupMassFormula.NSub I e z) μ := by sorry
