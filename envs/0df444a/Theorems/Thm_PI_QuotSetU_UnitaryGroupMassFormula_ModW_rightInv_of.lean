-- Prove2me | Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_ModW_rightInv_of
-- name    : PI.QuotSetU.UnitaryGroupMassFormula.ModW.rightInv_of
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:18:23.196634+00:00
-- url     : https://prove2.me/theorems/65d3ab60-48c6-5032-9601-ed3e0972f3a0
-- title:
--   Mod W: right Inv of
-- statement:
--   The Mod W construction uses the right Inv of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/ModCore.lean#L99-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/ModCore.lean#L99-L133

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_ModBase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_ModCore
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Topology
open scoped ENNReal NNReal Pointwise
noncomputable section
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.ModW
open PI MG
variable {m : ℕ} {G : Set (Matrix (Fin m) (Fin m) ℂ)} {hG : IsMatGroup G}

theorem PI.QuotSetU.UnitaryGroupMassFormula.ModW.rightInv_of (μ : Measure (MtM m)) (hμ : IsHaarOnM G μ)
    (h1 : ∀ g : MG G hG, Measure.modularCharacterFun g = 1) : IsRightInvM G μ := by sorry
