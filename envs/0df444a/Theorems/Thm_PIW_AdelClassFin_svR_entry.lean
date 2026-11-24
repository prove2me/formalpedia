-- Prove2me | Theorems.Thm_PIW_AdelClassFin_svR_entry
-- name    : PIW.AdelClassFin.svR_entry
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:53:01.188318+00:00
-- url     : https://prove2.me/theorems/3281066f-eeb6-4b01-9355-331f4ff5c180
-- title:
--   Adel Class Fin: sv R entry
-- statement:
--   The Adel Class Fin construction uses the sv R entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/SuccessiveVectorReal.lean#L27-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/SuccessiveVectorReal.lean#L27-L30

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

theorem PIW.AdelClassFin.svR_entry {o : Type*} [Fintype o] (X : Matrix o κ ℂ) (A : Matrix o o ℂ) (i j : κ) :
    (Xᴴ * A * X) i j = ∑ k, ∑ l, star (X k i) * A k l * X l j := by sorry
