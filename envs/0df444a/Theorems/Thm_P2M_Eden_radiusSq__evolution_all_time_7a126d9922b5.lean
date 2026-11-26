-- Prove2me | Theorems.Thm_P2M_Eden_radiusSq__evolution_all_time_7a126d9922b5
-- name    : P2M_Eden_radiusSq__evolution_all_time_7a126d9922b5
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:23:59.062135+00:00
-- url     : https://prove2.me/theorems/cfc4a04c-6cfc-5b14-8118-ba361246bdef
-- title:
--   P2 M Eden radius Sq  evolution all time 7a126d9922b5: P2 M Eden radius Sq  evolution all time 7a126d9922b5
-- statement:
--   The P2 M Eden radius Sq  evolution all time 7a126d9922b5 construction uses the P2 M Eden radius Sq  evolution all time 7a126d9922b5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/CompleteTrajectories.lean#L82-L86
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/CompleteTrajectories.lean#L82-L86

import Definitions.Def_Eden_Evolution
import Definitions.Def_Eden_RadialDynamics
import Definitions.Def_Eden_PhysicalRadius
import Definitions.Def_Eden_CompleteTrajectories
set_option autoImplicit true
noncomputable section
open Eden

theorem P2M_Eden_radiusSq__evolution_all_time_7a126d9922b5 (c t : ℝ) {p : PhaseSpace} (hp : p ∈ attractor) :
    radiusSq₁ (evolution c t p) = squaredRadiusEvolution t (radiusSq₁ p) := by sorry

alias «Eden».«radiusSq₁_evolution_all_time» := P2M_Eden_radiusSq__evolution_all_time_7a126d9922b5
