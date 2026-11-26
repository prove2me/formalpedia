-- Prove2me | Theorems.Thm_P2M_Eden_radiusSq__evolution_ce05ee2f5645
-- name    : P2M_Eden_radiusSq__evolution_ce05ee2f5645
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:07:35.332569+00:00
-- url     : https://prove2.me/theorems/b323496d-916a-4d18-b1a1-3d7de5a70b51
-- title:
--   P2 M Eden radius Sq  evolution ce05ee2f5645: P2 M Eden radius Sq  evolution ce05ee2f5645
-- statement:
--   The P2 M Eden radius Sq  evolution ce05ee2f5645 construction uses the P2 M Eden radius Sq  evolution ce05ee2f5645 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InvariantSets.lean#L34-L36
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InvariantSets.lean#L34-L36

import Definitions.Def_Eden_RadialDynamics
import Definitions.Def_Eden_Evolution
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Definitions.Def_Eden_InvariantSets
set_option autoImplicit true
noncomputable section
open Eden

theorem P2M_Eden_radiusSq__evolution_ce05ee2f5645 (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace) :
    radiusSq₂ (evolution c t p) = squaredRadiusEvolution t (radiusSq₂ p) := by sorry

alias «Eden».«radiusSq₂_evolution» := P2M_Eden_radiusSq__evolution_ce05ee2f5645
