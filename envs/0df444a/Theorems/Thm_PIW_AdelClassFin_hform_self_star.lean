-- Prove2me | Theorems.Thm_PIW_AdelClassFin_hform_self_star
-- name    : PIW.AdelClassFin.hform_self_star
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:48:02.919178+00:00
-- url     : https://prove2.me/theorems/a062389d-5801-403d-9f80-17b1ca603b0e
-- title:
--   Adel Class Fin: hform self star
-- statement:
--   The Adel Class Fin construction uses the hform self star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/HformSelfStar.lean#L105-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/HformSelfStar.lean#L105-L113

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_StGenusOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HformSelfStar
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
open Formalism.UG NumberField
open scoped Matrix
variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem PIW.AdelClassFin.hform_self_star {m : ℕ} (J : Matrix (Fin m) (Fin m) E) (hJ : IsHerm (starRingEnd E) J)
    (x : Fin m → E) : star (hform (starRingEnd E) J x x) = hform (starRingEnd E) J x x := by sorry
