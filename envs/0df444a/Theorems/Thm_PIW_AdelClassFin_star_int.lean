-- Prove2me | Theorems.Thm_PIW_AdelClassFin_star_int
-- name    : PIW.AdelClassFin.star_int
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:49:17.735498+00:00
-- url     : https://prove2.me/theorems/5b8e060c-eac6-4972-b2ec-8856a3926a53
-- title:
--   Adel Class Fin: star int
-- statement:
--   The Adel Class Fin construction uses the star int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/HformSmulRight.lean#L88-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/HformSmulRight.lean#L88-L99

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HformSelfStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_IdealMulPrincipal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HformSmulRight
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

theorem PIW.AdelClassFin.star_int {E : Type} [Field E] [NumberField E] [StarRing E] (q : 𝓞 E) :
    ∃ q' : 𝓞 E, algebraMap (𝓞 E) E q' = star (algebraMap (𝓞 E) E q) := by sorry
