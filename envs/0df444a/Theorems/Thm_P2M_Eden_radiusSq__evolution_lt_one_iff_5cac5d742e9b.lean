-- Prove2me | Theorems.Thm_P2M_Eden_radiusSq__evolution_lt_one_iff_5cac5d742e9b
-- name    : P2M_Eden_radiusSq__evolution_lt_one_iff_5cac5d742e9b
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:08:17.449368+00:00
-- url     : https://prove2.me/theorems/b7d3698a-0175-4c2a-a4ff-0d3e1a7fa887
-- title:
--   P2 M Eden radius Sq  evolution lt one iff 5cac5d742e9b: P2 M Eden radius Sq  evolution lt one iff 5cac5d742e9b
-- statement:
--   The P2 M Eden radius Sq  evolution lt one iff 5cac5d742e9b construction uses the P2 M Eden radius Sq  evolution lt one iff 5cac5d742e9b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Nontransitivity.lean#L69-L71
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Nontransitivity.lean#L69-L71

import Definitions.Def_Eden_PeriodicOrbits
import Definitions.Def_Eden_StrictInvariance
import Definitions.Def_Eden_Nontransitivity
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem P2M_Eden_radiusSq__evolution_lt_one_iff_5cac5d742e9b (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace) :
    radiusSq₁ (evolution c t p) < 1 ↔ radiusSq₁ p < 1 := by sorry

alias «Eden».«radiusSq₁_evolution_lt_one_iff» := P2M_Eden_radiusSq__evolution_lt_one_iff_5cac5d742e9b
