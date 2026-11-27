-- Prove2me | Theorems.Thm_PIW_AdelClassFin_isImg_trans
-- name    : PIW.AdelClassFin.isImg_trans
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:50:06.210444+00:00
-- url     : https://prove2.me/theorems/0ad7a32e-b743-4e51-bcee-fae87deed2b0
-- title:
--   Adel Class Fin: is Img trans
-- statement:
--   The Adel Class Fin construction uses the is Img trans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/IsImgTrans.lean#L28-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/IsImgTrans.lean#L28-L42

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_StGenusOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_IsImgTrans
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.AdelClassFin
open Formalism.MainNotions.S PI.AdelClassFin NumberField
open scoped TensorProduct Matrix

theorem PIW.AdelClassFin.isImg_trans {E : Type} [Field E] [NumberField E] {n : ℕ} {γ γ₀ : GL (Fin n) E}
    {M₀ M₁ M : Submodule (𝓞 E) (Fin n → E)} (h₁ : IsImg γ₀ M₀ M₁) (h : IsImg γ M₀ M) :
    IsImg (γ * γ₀⁻¹) M₁ M := by sorry
