-- Prove2me | Theorems.Thm_P2M_Eden_one_lt_radiusSq__evolution_iff_356d16ba0e6d
-- name    : P2M_Eden_one_lt_radiusSq__evolution_iff_356d16ba0e6d
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:05:04.260567+00:00
-- url     : https://prove2.me/theorems/15361e3d-2c51-4bac-bb19-24e3ba8ef434
-- title:
--   P2 M Eden one lt radius Sq  evolution iff 356d16ba0e6d: P2 M Eden one lt radius Sq  evolution iff 356d16ba0e6d
-- statement:
--   The P2 M Eden one lt radius Sq  evolution iff 356d16ba0e6d construction uses the P2 M Eden one lt radius Sq  evolution iff 356d16ba0e6d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Nontransitivity.lean#L73-L75
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Nontransitivity.lean#L73-L75

import Definitions.Def_Eden_PeriodicOrbits
import Definitions.Def_Eden_StrictInvariance
import Definitions.Def_Eden_Nontransitivity
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem P2M_Eden_one_lt_radiusSq__evolution_iff_356d16ba0e6d (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace) :
    1 < radiusSq₁ (evolution c t p) ↔ 1 < radiusSq₁ p := by sorry

alias «Eden».«one_lt_radiusSq₁_evolution_iff» := P2M_Eden_one_lt_radiusSq__evolution_iff_356d16ba0e6d
