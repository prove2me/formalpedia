-- Prove2me | Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_xxw_entry
-- name    : PI.TwistedEisensteinNonvanishing.W.xxw_entry
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:22:20.310186+00:00
-- url     : https://prove2.me/theorems/f1e14b1d-e17b-4793-9cc9-0619b4a90ad8
-- title:
--   W: xxw entry
-- statement:
--   The W construction uses the xxw entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/FreeCoordinateAffineInvertible.lean#L29-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/FreeCoordinateAffineInvertible.lean#L29-L35

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

theorem PI.TwistedEisensteinNonvanishing.W.xxw_entry {n' c' n c : ℕ} (xj : (Fin n' → E) →ₗ[E] (Fin n → E)) (t : FC n' c' n c → E) (s : Fin (n' + c')) (l : Fin (n + c)) :
    xx1 xj t (Pi.single s 1) l =
      if hf : IsFree n' n c l.1 s.1 then t ⟨(l, s), hf⟩
      else if hs : s.1 < n' then (if hl : l.1 < n then LinearMap.toMatrix' xj ⟨l.1, hl⟩ ⟨s.1, hs⟩ else 0)
      else if l.1 = n + (s.1 - n') then 1 else 0 := by sorry
