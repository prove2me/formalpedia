-- Prove2me | Theorems.Thm_PIW_AdelClassFin_spl_ker
-- name    : PIW.AdelClassFin.spl_ker
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:48:31.662411+00:00
-- url     : https://prove2.me/theorems/e1892c29-83b6-4db6-9d4a-0822ea284e60
-- title:
--   Adel Class Fin: spl ker
-- statement:
--   The Adel Class Fin construction uses the spl ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/SplHformZero.lean#L13-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/SplHformZero.lean#L13-L19

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

theorem PIW.AdelClassFin.spl_ker {E : Type} [Field E] [StarRing E] {m k : ℕ} (J : Matrix (Fin m) (Fin m) E)
    (V : Matrix (Fin m) (Fin k) E)
    (hΓ : (cT (starRingEnd E) V * J * V).det ≠ 0) (w : Fin m → E) :
    (cT (starRingEnd E) V * J) *ᵥ (w - V *ᵥ ((cT (starRingEnd E) V * J * V)⁻¹ *ᵥ
      ((cT (starRingEnd E) V * J) *ᵥ w))) = 0 := by sorry
