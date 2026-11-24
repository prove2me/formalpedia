-- Prove2me | Theorems.Thm_PIW_AdelClassFin_hform_smul
-- name    : PIW.AdelClassFin.hform_smul
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T13:13:19.802719+00:00
-- url     : https://prove2.me/theorems/15705d56-e6ff-45ec-8ef5-2e1535f84553
-- title:
--   Adel Class Fin: hform smul
-- statement:
--   The Adel Class Fin construction uses the hform smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/HformSelfStar.lean#L99-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/HformSelfStar.lean#L99-L103

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

theorem PIW.AdelClassFin.hform_smul {m : ℕ} (J : Matrix (Fin m) (Fin m) E) (c c' : E) (x y : Fin m → E) :
    hform (starRingEnd E) J (c • x) (c' • y) = star c * c' * hform (starRingEnd E) J x y := by sorry
