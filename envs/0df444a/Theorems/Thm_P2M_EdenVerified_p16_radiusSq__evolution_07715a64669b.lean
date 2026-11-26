-- Prove2me | Theorems.Thm_P2M_EdenVerified_p16_radiusSq__evolution_07715a64669b
-- name    : P2M_EdenVerified_p16_radiusSq__evolution_07715a64669b
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:46:06.184367+00:00
-- url     : https://prove2.me/theorems/a3aac7a4-e35c-414f-859c-131af08c5c95
-- title:
--   P2 M Eden Verified p16 radius Sq  evolution 07715a64669b: P2 M Eden Verified p16 radius Sq  evolution 07715a64669b
-- statement:
--   The P2 M Eden Verified p16 radius Sq  evolution 07715a64669b construction uses the P2 M Eden Verified p16 radius Sq  evolution 07715a64669b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1481-L1484
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1481-L1484

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem P2M_EdenVerified_p16_radiusSq__evolution_07715a64669b :
    ∀ (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace),
    radiusSq₁ (evolution c t p) = squaredRadiusEvolution t (radiusSq₁ p) := by sorry

alias «EdenVerified».«p16_radiusSq₁_evolution» := P2M_EdenVerified_p16_radiusSq__evolution_07715a64669b
