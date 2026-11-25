-- Prove2me | Theorems.Thm_PIW_AdelClassFin_svR_trace
-- name    : PIW.AdelClassFin.svR_trace
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:47:59.469806+00:00
-- url     : https://prove2.me/theorems/c4a7c9c4-1af2-428b-a80a-6ce01c7c20da
-- title:
--   Adel Class Fin: sv R trace
-- statement:
--   The Adel Class Fin construction uses the sv R trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/SuccessiveVectorReal.lean#L67-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/SuccessiveVectorReal.lean#L67-L77

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

theorem PIW.AdelClassFin.svR_trace (hst : ∀ (φ : E →+* ℂ) (a : E), φ (star a) = starRingEnd ℂ (φ a)) {m N : ℕ}
    (J : Matrix (Fin m) (Fin m) E) (e : Fin N → Fin m → E) :
    (gramTr J e).map (Rat.castHom ℂ) = ∑ φ, (svP e φ)ᴴ * J.map φ * svP e φ := by sorry
