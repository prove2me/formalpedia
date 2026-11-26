-- Prove2me | Theorems.Thm_P2M_EdenVerified_p01_radius__evolution_5491b9e515dc
-- name    : P2M_EdenVerified_p01_radius__evolution_5491b9e515dc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:27:47.011123+00:00
-- url     : https://prove2.me/theorems/5793bae2-4be9-4707-9681-67fb06450baf
-- title:
--   P2 M Eden Verified p01 radius  evolution 5491b9e515dc: P2 M Eden Verified p01 radius  evolution 5491b9e515dc
-- statement:
--   The P2 M Eden Verified p01 radius  evolution 5491b9e515dc construction uses the P2 M Eden Verified p01 radius  evolution 5491b9e515dc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L726-L729
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L726-L729

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem P2M_EdenVerified_p01_radius__evolution_5491b9e515dc :
    ∀ (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace),
    Real.sqrt (radiusSq₁ (evolution c t p)) = radiusEvolution t (Real.sqrt (radiusSq₁ p)) := by sorry

alias «EdenVerified».«p01_radius₁_evolution» := P2M_EdenVerified_p01_radius__evolution_5491b9e515dc
