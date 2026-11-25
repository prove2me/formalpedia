-- Prove2me | Theorems.Thm_PIW_AdelClassFin_stH_of_hl
-- name    : PIW.AdelClassFin.stH_of_hl
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:48:53.404704+00:00
-- url     : https://prove2.me/theorems/14fb72dd-79a2-4887-9131-57ff638778ab
-- title:
--   Adel Class Fin: st H of hl
-- statement:
--   The Adel Class Fin construction uses the st H of hl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/HformSelfStar.lean#L182-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/HformSelfStar.lean#L182-L242

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

theorem PIW.AdelClassFin.stH_of_hl (hHL : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
    [Algebra F E], Formalism.BasicNotions.CMData F E → ∀ m, HL E m) : StH := by sorry
