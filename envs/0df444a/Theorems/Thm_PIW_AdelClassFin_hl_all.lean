-- Prove2me | Theorems.Thm_PIW_AdelClassFin_hl_all
-- name    : PIW.AdelClassFin.hl_all
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T06:01:57.965796+00:00
-- url     : https://prove2.me/theorems/35627911-4d1c-5840-b22c-b095f5fae7d2
-- title:
--   Adel Class Fin: hl all
-- statement:
--   The Adel Class Fin construction uses the hl all property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/HformSelfStar.lean#L172-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/HformSelfStar.lean#L172-L180

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

theorem PIW.AdelClassFin.hl_all (hS : PartShort) (hU : PartUnits) (hI : PartIso) (hP : PartSplit)
    (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : Formalism.BasicNotions.CMData F E) (m : ℕ) : HL E m := by sorry
