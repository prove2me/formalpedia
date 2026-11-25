-- Prove2me | Theorems.Thm_PIW_AdelClassFin_svBig_block
-- name    : PIW.AdelClassFin.svBig_block
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:47:48.212752+00:00
-- url     : https://prove2.me/theorems/2b75de1a-8ebe-4ce9-bf99-a92105d93046
-- title:
--   Adel Class Fin: sv Big block
-- statement:
--   The Adel Class Fin construction uses the sv Big block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/SuccessiveVectorReal.lean#L44-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/SuccessiveVectorReal.lean#L44-L52

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

theorem PIW.AdelClassFin.svBig_block [DecidableEq (E →+* ℂ)] {m N : ℕ} (e : Fin N → Fin m → E)
    (A : (E →+* ℂ) → Matrix (Fin m) (Fin m) ℂ) :
    (svBig e)ᴴ * blockDiagonal A * svBig e = ∑ φ, (svP e φ)ᴴ * A φ * svP e φ := by sorry
