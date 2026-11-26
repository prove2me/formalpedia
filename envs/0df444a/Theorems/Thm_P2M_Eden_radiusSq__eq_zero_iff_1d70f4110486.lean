-- Prove2me | Theorems.Thm_P2M_Eden_radiusSq__eq_zero_iff_1d70f4110486
-- name    : P2M_Eden_radiusSq__eq_zero_iff_1d70f4110486
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:43:53.672067+00:00
-- url     : https://prove2.me/theorems/32d224ac-3f47-5132-bc4d-5f5c172feb15
-- title:
--   P2 M Eden radius Sq  eq zero iff 1d70f4110486: P2 M Eden radius Sq  eq zero iff 1d70f4110486
-- statement:
--   The P2 M Eden radius Sq  eq zero iff 1d70f4110486 construction uses the P2 M Eden radius Sq  eq zero iff 1d70f4110486 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/RadialReturns.lean#L49-L56
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/RadialReturns.lean#L49-L56

import Definitions.Def_Eden_InvariantSets
import Definitions.Def_Eden_StationaryFactors
import Definitions.Def_Eden_RadialReturns
set_option autoImplicit true
noncomputable section
open Eden

theorem P2M_Eden_radiusSq__eq_zero_iff_1d70f4110486 (p : PhaseSpace) :
    radiusSq₁ p = 0 ↔ p 0 = 0 ∧ p 1 = 0 := by sorry

alias «Eden».«radiusSq₁_eq_zero_iff» := P2M_Eden_radiusSq__eq_zero_iff_1d70f4110486
