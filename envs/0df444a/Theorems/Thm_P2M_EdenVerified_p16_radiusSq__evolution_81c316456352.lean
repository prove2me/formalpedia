-- Prove2me | Theorems.Thm_P2M_EdenVerified_p16_radiusSq__evolution_81c316456352
-- name    : P2M_EdenVerified_p16_radiusSq__evolution_81c316456352
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:46:01.977706+00:00
-- url     : https://prove2.me/theorems/fcc7856d-8054-4a95-b9c8-07b5cc653387
-- title:
--   P2 M Eden Verified p16 radius Sq  evolution 81c316456352: P2 M Eden Verified p16 radius Sq  evolution 81c316456352
-- statement:
--   The P2 M Eden Verified p16 radius Sq  evolution 81c316456352 construction uses the P2 M Eden Verified p16 radius Sq  evolution 81c316456352 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1486-L1489
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1486-L1489

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem P2M_EdenVerified_p16_radiusSq__evolution_81c316456352 :
    ∀ (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace),
    radiusSq₂ (evolution c t p) = squaredRadiusEvolution t (radiusSq₂ p) := by sorry

alias «EdenVerified».«p16_radiusSq₂_evolution» := P2M_EdenVerified_p16_radiusSq__evolution_81c316456352
