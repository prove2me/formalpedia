-- Prove2me | Theorems.Thm_PIW_AdelClassFin_isHerm_iff
-- name    : PIW.AdelClassFin.isHerm_iff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:50:15.240378+00:00
-- url     : https://prove2.me/theorems/202e19a2-3aa8-48bd-bd45-9fefae753be8
-- title:
--   Adel Class Fin: is Herm iff
-- statement:
--   The Adel Class Fin construction uses the is Herm iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/HformSingleLeft.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/HformSingleLeft.lean#L18-L20

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HformSelfStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HformSingleLeft
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
open Formalism.UG
open scoped Matrix
variable {E : Type} [Field E] [StarRing E]

theorem PIW.AdelClassFin.isHerm_iff {n : Type} (J : Matrix n n E) : IsHerm (starRingEnd E) J ↔ Jᴴ = J := by sorry
