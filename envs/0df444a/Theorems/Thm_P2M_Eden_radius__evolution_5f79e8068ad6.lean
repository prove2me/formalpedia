-- Prove2me | Theorems.Thm_P2M_Eden_radius__evolution_5f79e8068ad6
-- name    : P2M_Eden_radius__evolution_5f79e8068ad6
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:14:39.940053+00:00
-- url     : https://prove2.me/theorems/befc3981-f0a9-5227-9c0b-c8aa0edf757a
-- title:
--   P2 M Eden radius  evolution 5f79e8068ad6: P2 M Eden radius  evolution 5f79e8068ad6
-- statement:
--   The P2 M Eden radius  evolution 5f79e8068ad6 construction uses the P2 M Eden radius  evolution 5f79e8068ad6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PhysicalRadius.lean#L105-L108
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PhysicalRadius.lean#L105-L108

import Definitions.Def_Eden_InvariantSets
import Definitions.Def_Eden_GrowthRates
import Definitions.Def_Eden_PhysicalRadius
set_option autoImplicit true
noncomputable section
open Filter Set
open scoped Topology
open Eden

theorem P2M_Eden_radius__evolution_5f79e8068ad6 (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace) :
    Real.sqrt (radiusSq₁ (evolution c t p)) = radiusEvolution t (Real.sqrt (radiusSq₁ p)) := by sorry

alias «Eden».«radius₁_evolution» := P2M_Eden_radius__evolution_5f79e8068ad6
