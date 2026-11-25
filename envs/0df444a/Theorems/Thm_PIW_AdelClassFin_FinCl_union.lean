-- Prove2me | Theorems.Thm_PIW_AdelClassFin_FinCl_union
-- name    : PIW.AdelClassFin.FinCl.union
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:47:34.154302+00:00
-- url     : https://prove2.me/theorems/03e9bde2-248e-4fec-a1d8-ef22bf046bb9
-- title:
--   Fin Cl: union
-- statement:
--   The Fin Cl construction uses the union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/HformSelfStar.lean#L88-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/HformSelfStar.lean#L88-L97

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

theorem PIW.AdelClassFin.FinCl.union {m : ℕ} {S S' : Set (Matrix (Fin m) (Fin m) E × Submodule (𝓞 E) (Fin m → E))}
    (h : FinCl S) (h' : FinCl S') : FinCl (S ∪ S') := by sorry
