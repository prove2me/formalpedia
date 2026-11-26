-- Prove2me | Theorems.Thm_P2M_EdenVerified_p01_radius__evolution_d91fbbccba93
-- name    : P2M_EdenVerified_p01_radius__evolution_d91fbbccba93
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:27:51.485612+00:00
-- url     : https://prove2.me/theorems/4e8e6702-c7ad-56cb-a357-d931826acb2a
-- title:
--   P2 M Eden Verified p01 radius  evolution d91fbbccba93: P2 M Eden Verified p01 radius  evolution d91fbbccba93
-- statement:
--   The P2 M Eden Verified p01 radius  evolution d91fbbccba93 construction uses the P2 M Eden Verified p01 radius  evolution d91fbbccba93 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L731-L734
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L731-L734

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem P2M_EdenVerified_p01_radius__evolution_d91fbbccba93 :
    ∀ (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace),
    Real.sqrt (radiusSq₂ (evolution c t p)) = radiusEvolution t (Real.sqrt (radiusSq₂ p)) := by sorry

alias «EdenVerified».«p01_radius₂_evolution» := P2M_EdenVerified_p01_radius__evolution_d91fbbccba93
