-- Prove2me | Theorems.Thm_PIW_AdelClassFin_spl_cross
-- name    : PIW.AdelClassFin.spl_cross
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T13:54:59.086635+00:00
-- url     : https://prove2.me/theorems/8234507c-ab3e-45f5-bf2f-bfdbcbf2c176
-- title:
--   Adel Class Fin: spl cross
-- statement:
--   The Adel Class Fin construction uses the spl cross property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/SplHformZero.lean#L21-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/SplHformZero.lean#L21-L34

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HformSelfStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_PartSplitOfOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HformSingleLeft
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_SplHformZero
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

theorem PIW.AdelClassFin.spl_cross {E : Type} [Field E] [StarRing E] {m k n : ℕ} (J : Matrix (Fin m) (Fin m) E)
    (V : Matrix (Fin m) (Fin k) E) (U : Matrix (Fin m) (Fin n) E) (h : cT (starRingEnd E) V * J * U = 0)
    (c : Fin k → E) (w : Fin n → E) : hform (starRingEnd E) J (V *ᵥ c) (U *ᵥ w) = 0 := by sorry
