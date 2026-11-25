-- Prove2me | Theorems.Thm_PIW_AdelClassFin_hform_exists_ne
-- name    : PIW.AdelClassFin.hform_exists_ne
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:48:46.779884+00:00
-- url     : https://prove2.me/theorems/4e6d2c7b-6370-4882-a0be-0a23bf015ff6
-- title:
--   Adel Class Fin: hform exists ne
-- statement:
--   The Adel Class Fin construction uses the hform exists ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/HformSmulRight.lean#L58-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/HformSmulRight.lean#L58-L84

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
variable {E : Type} [Field E] [StarRing E] {m : ℕ} (J : Matrix (Fin m) (Fin m) E)

theorem PIW.AdelClassFin.hform_exists_ne (hdet : J.det ≠ 0) (S : Set (Fin m → E)) (hS : Submodule.span E S = ⊤)
    {x : Fin m → E} (hx : x ≠ 0) : ∃ z ∈ S, hform (starRingEnd E) J x z ≠ 0 := by sorry
