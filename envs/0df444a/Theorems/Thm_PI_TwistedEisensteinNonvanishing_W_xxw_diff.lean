-- Prove2me | Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_xxw_diff
-- name    : PI.TwistedEisensteinNonvanishing.W.xxw_diff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:42:57.88693+00:00
-- url     : https://prove2.me/theorems/7caa519b-c3fb-483c-9c36-c684b95c0a3a
-- title:
--   W: xxw diff
-- statement:
--   The W construction uses the xxw diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/FreeCoordinateAffineInvertible.lean#L218-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/FreeCoordinateAffineInvertible.lean#L218-L223

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IaDivDown
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_FreeCoordinateAffineInvertible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Module
noncomputable section
open PI PI.TwistedEisensteinNonvanishing PI.TwistedEisensteinNonvanishing.W
open Loc LocE
variable {E : Type} [Field E]

theorem PI.TwistedEisensteinNonvanishing.W.xxw_diff {n' c' n c : ℕ} (t : FC n' c' n c → E) (s : Fin (n' + c')) :
    xx1 (0 : (Fin n' → E) →ₗ[E] (Fin n → E)) t (Pi.single s 1) - xx1 (0 : (Fin n' → E) →ₗ[E] (Fin n → E)) 0 (Pi.single s 1) =
      fun l => if hf : IsFree n' n c l.1 s.1 then t ⟨(l, s), hf⟩ else 0 := by sorry
