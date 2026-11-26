-- Prove2me | Theorems.Thm_P2M_Eden_radiusSq__evolution_all_time_13def274be72
-- name    : P2M_Eden_radiusSq__evolution_all_time_13def274be72
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:24:03.571831+00:00
-- url     : https://prove2.me/theorems/a51375c7-5421-526e-8833-e3a19a46285d
-- title:
--   P2 M Eden radius Sq  evolution all time 13def274be72: P2 M Eden radius Sq  evolution all time 13def274be72
-- statement:
--   The P2 M Eden radius Sq  evolution all time 13def274be72 construction uses the P2 M Eden radius Sq  evolution all time 13def274be72 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/CompleteTrajectories.lean#L88-L92
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/CompleteTrajectories.lean#L88-L92

import Definitions.Def_Eden_Evolution
import Definitions.Def_Eden_RadialDynamics
import Definitions.Def_Eden_PhysicalRadius
import Definitions.Def_Eden_CompleteTrajectories
set_option autoImplicit true
noncomputable section
open Eden

theorem P2M_Eden_radiusSq__evolution_all_time_13def274be72 (c t : ℝ) {p : PhaseSpace} (hp : p ∈ attractor) :
    radiusSq₂ (evolution c t p) = squaredRadiusEvolution t (radiusSq₂ p) := by sorry

alias «Eden».«radiusSq₂_evolution_all_time» := P2M_Eden_radiusSq__evolution_all_time_13def274be72
