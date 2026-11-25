-- Prove2me | Theorems.Thm_PIW_AdelClassFin_hform_single
-- name    : PIW.AdelClassFin.hform_single
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:48:41.349798+00:00
-- url     : https://prove2.me/theorems/9e8eeb62-8e8c-42f0-bdc3-674abf858d6e
-- title:
--   Adel Class Fin: hform single
-- statement:
--   The Adel Class Fin construction uses the hform single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/HformSingleLeft.lean#L48-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/HformSingleLeft.lean#L48-L51

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

theorem PIW.AdelClassFin.hform_single {n : Type} [Fintype n] [DecidableEq n] (J : Matrix n n E) (i j : n) :
    hform (starRingEnd E) J (Pi.single i 1) (Pi.single j 1) = J i j := by sorry
