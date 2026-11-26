-- Prove2me | Theorems.Thm_P2M_Eden_radiusSq__evolution_eq_one_iff_e3aa1969fb2c
-- name    : P2M_Eden_radiusSq__evolution_eq_one_iff_e3aa1969fb2c
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:08:11.006353+00:00
-- url     : https://prove2.me/theorems/6eaa7cfd-d81a-5823-8cfb-e518bc7ad51d
-- title:
--   P2 M Eden radius Sq  evolution eq one iff e3aa1969fb2c: P2 M Eden radius Sq  evolution eq one iff e3aa1969fb2c
-- statement:
--   The P2 M Eden radius Sq  evolution eq one iff e3aa1969fb2c construction uses the P2 M Eden radius Sq  evolution eq one iff e3aa1969fb2c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Nontransitivity.lean#L77-L81
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Nontransitivity.lean#L77-L81

import Definitions.Def_Eden_PeriodicOrbits
import Definitions.Def_Eden_StrictInvariance
import Definitions.Def_Eden_Nontransitivity
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem P2M_Eden_radiusSq__evolution_eq_one_iff_e3aa1969fb2c (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace) :
    radiusSq₁ (evolution c t p) = 1 ↔ radiusSq₁ p = 1 := by sorry

alias «Eden».«radiusSq₁_evolution_eq_one_iff» := P2M_Eden_radiusSq__evolution_eq_one_iff_e3aa1969fb2c
