-- Prove2me | Theorems.Thm_P2M_CompanionTheory_D_Upq_QuotSetU_cdiag_mul__260c206f0917
-- name    : P2M_CompanionTheory_D_Upq_QuotSetU_cdiag_mul__260c206f0917
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T02:42:46.063474+00:00
-- url     : https://prove2.me/theorems/77e06234-68a8-4c7e-b62d-1a8a545b444c
-- title:
--   P2 M Companion Theory D Upq Quot Set U cdiag mul  260c206f0917: P2 M Companion Theory D Upq Quot Set U cdiag mul  260c206f0917
-- statement:
--   The P2 M Companion Theory D Upq Quot Set U cdiag mul  260c206f0917 construction uses the P2 M Companion Theory D Upq Quot Set U cdiag mul  260c206f0917 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SecondCountableQuotients/NContract.lean#L47-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SecondCountableQuotients/NContract.lean#L47-L49

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_SGroup
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_NContract
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq CompanionTheory.D.Upq.QuotSetU
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.SW
variable {k r : ℕ}
local notation "𝕄" => Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ

theorem P2M_CompanionTheory_D_Upq_QuotSetU_cdiag_mul__260c206f0917 {t : ℝ} (ht : t ≠ 0) : cdiag k r t⁻¹ * cdiag k r t = 1 := by sorry

alias «CompanionTheory».«D».«Upq».«QuotSetU».«cdiag_mul'» := P2M_CompanionTheory_D_Upq_QuotSetU_cdiag_mul__260c206f0917
