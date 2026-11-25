-- Prove2me | Theorems.Thm_PIW_AdelClassFin_svR_form
-- name    : PIW.AdelClassFin.svR_form
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:48:35.645178+00:00
-- url     : https://prove2.me/theorems/5c02557c-a343-4708-a59d-d4fbecb54f68
-- title:
--   Adel Class Fin: sv R form
-- statement:
--   The Adel Class Fin construction uses the sv R form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/SuccessiveVectorReal.lean#L15-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/SuccessiveVectorReal.lean#L15-L18

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_PartShortOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_SuccessiveVectorReal
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
open Formalism.UG NumberField Matrix
open scoped ComplexOrder
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem PIW.AdelClassFin.svR_form {o : Type*} [Fintype o] (X : Matrix o κ ℂ) (A : Matrix o o ℂ) (v : κ → ℂ) :
    star (X *ᵥ v) ⬝ᵥ (A *ᵥ (X *ᵥ v)) = star v ⬝ᵥ ((Xᴴ * A * X) *ᵥ v) := by sorry
