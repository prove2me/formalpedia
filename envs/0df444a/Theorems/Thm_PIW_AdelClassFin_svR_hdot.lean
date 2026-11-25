-- Prove2me | Theorems.Thm_PIW_AdelClassFin_svR_hdot
-- name    : PIW.AdelClassFin.svR_hdot
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:48:34.680876+00:00
-- url     : https://prove2.me/theorems/de13b79e-4586-472a-b5d6-2f60e98c0f45
-- title:
--   Adel Class Fin: sv R hdot
-- statement:
--   The Adel Class Fin construction uses the sv R hdot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/SuccessiveVectorReal.lean#L60-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/SuccessiveVectorReal.lean#L60-L65

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
variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem PIW.AdelClassFin.svR_hdot (hst : ∀ (φ : E →+* ℂ) (a : E), φ (star a) = starRingEnd ℂ (φ a)) {m : ℕ}
    (J : Matrix (Fin m) (Fin m) E) (φ : E →+* ℂ) (x y : Fin m → E) :
    φ (hform (starRingEnd E) J x y) =
      star (fun k => φ (x k)) ⬝ᵥ (J.map φ *ᵥ fun l => φ (y l)) := by sorry
