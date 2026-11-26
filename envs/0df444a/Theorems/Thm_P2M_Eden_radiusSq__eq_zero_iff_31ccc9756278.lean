-- Prove2me | Theorems.Thm_P2M_Eden_radiusSq__eq_zero_iff_31ccc9756278
-- name    : P2M_Eden_radiusSq__eq_zero_iff_31ccc9756278
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:43:55.825146+00:00
-- url     : https://prove2.me/theorems/c65641ba-71ec-519d-9101-5984c5b26e40
-- title:
--   P2 M Eden radius Sq  eq zero iff 31ccc9756278: P2 M Eden radius Sq  eq zero iff 31ccc9756278
-- statement:
--   The P2 M Eden radius Sq  eq zero iff 31ccc9756278 construction uses the P2 M Eden radius Sq  eq zero iff 31ccc9756278 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/RadialReturns.lean#L58-L65
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/RadialReturns.lean#L58-L65

import Definitions.Def_Eden_InvariantSets
import Definitions.Def_Eden_StationaryFactors
import Definitions.Def_Eden_RadialReturns
set_option autoImplicit true
noncomputable section
open Eden

theorem P2M_Eden_radiusSq__eq_zero_iff_31ccc9756278 (p : PhaseSpace) :
    radiusSq₂ p = 0 ↔ p 2 = 0 ∧ p 3 = 0 := by sorry

alias «Eden».«radiusSq₂_eq_zero_iff» := P2M_Eden_radiusSq__eq_zero_iff_31ccc9756278
