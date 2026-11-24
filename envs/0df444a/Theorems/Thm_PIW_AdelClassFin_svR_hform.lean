-- Prove2me | Theorems.Thm_PIW_AdelClassFin_svR_hform
-- name    : PIW.AdelClassFin.svR_hform
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:52:30.033274+00:00
-- url     : https://prove2.me/theorems/3edc47c7-84dc-4c3b-b872-002bf43a4012
-- title:
--   Adel Class Fin: sv R hform
-- statement:
--   The Adel Class Fin construction uses the sv R hform property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/SuccessiveVectorReal.lean#L54-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/SuccessiveVectorReal.lean#L54-L58

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

theorem PIW.AdelClassFin.svR_hform (hst : ∀ (φ : E →+* ℂ) (a : E), φ (star a) = starRingEnd ℂ (φ a)) {m : ℕ}
    (J : Matrix (Fin m) (Fin m) E) (φ : E →+* ℂ) (x y : Fin m → E) :
    φ (hform (starRingEnd E) J x y) = ∑ k, ∑ l, star (φ (x k)) * φ (J k l) * φ (y l) := by sorry
