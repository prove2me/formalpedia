-- Prove2me | Theorems.Thm_P2M_PI_QuotSetU_UnitaryGroupMassFormula_SW_inv_mul_UH__f897c67e29e4
-- name    : P2M_PI_QuotSetU_UnitaryGroupMassFormula_SW_inv_mul_UH__f897c67e29e4
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T02:27:19.798448+00:00
-- url     : https://prove2.me/theorems/75deeca4-3282-4dcd-86fd-b58cc57827e3
-- title:
--   P2 M PI Quot Set U Unitary Group Mass Formula SW inv mul UH  f897c67e29e4: P2 M PI Quot Set U Unitary Group Mass Formula SW inv mul UH  f897c67e29e4
-- statement:
--   The P2 M PI Quot Set U Unitary Group Mass Formula SW inv mul UH  f897c67e29e4 construction uses the P2 M PI Quot Set U Unitary Group Mass Formula SW inv mul UH  f897c67e29e4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/SBasic.lean#L95-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/SBasic.lean#L95-L98

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SsetGroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.SW
open PI PI.QuotSetU
variable {k r : ℕ}

theorem P2M_PI_QuotSetU_UnitaryGroupMassFormula_SW_inv_mul_UH__f897c67e29e4 {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r)) :
    g⁻¹ * g = 1 := by sorry

alias «PI».«QuotSetU».«UnitaryGroupMassFormula».«SW».«inv_mul_UH'» := P2M_PI_QuotSetU_UnitaryGroupMassFormula_SW_inv_mul_UH__f897c67e29e4
