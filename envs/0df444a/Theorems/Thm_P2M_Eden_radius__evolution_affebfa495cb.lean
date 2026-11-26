-- Prove2me | Theorems.Thm_P2M_Eden_radius__evolution_affebfa495cb
-- name    : P2M_Eden_radius__evolution_affebfa495cb
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:15:36.877729+00:00
-- url     : https://prove2.me/theorems/eed02e73-6bb0-5533-9bdf-88f1c2dd0c70
-- title:
--   P2 M Eden radius  evolution affebfa495cb: P2 M Eden radius  evolution affebfa495cb
-- statement:
--   The P2 M Eden radius  evolution affebfa495cb construction uses the P2 M Eden radius  evolution affebfa495cb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PhysicalRadius.lean#L110-L113
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PhysicalRadius.lean#L110-L113

import Definitions.Def_Eden_InvariantSets
import Definitions.Def_Eden_GrowthRates
import Definitions.Def_Eden_PhysicalRadius
set_option autoImplicit true
noncomputable section
open Filter Set
open scoped Topology
open Eden

theorem P2M_Eden_radius__evolution_affebfa495cb (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace) :
    Real.sqrt (radiusSq₂ (evolution c t p)) = radiusEvolution t (Real.sqrt (radiusSq₂ p)) := by sorry

alias «Eden».«radius₂_evolution» := P2M_Eden_radius__evolution_affebfa495cb
