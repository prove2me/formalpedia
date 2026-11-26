-- Prove2me | Theorems.Thm_P2M_Eden_radiusSq__evolution_4de951b85a7e
-- name    : P2M_Eden_radiusSq__evolution_4de951b85a7e
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:07:09.470012+00:00
-- url     : https://prove2.me/theorems/961c0e7a-3b80-47f4-8721-5d99a2d5824e
-- title:
--   P2 M Eden radius Sq  evolution 4de951b85a7e: P2 M Eden radius Sq  evolution 4de951b85a7e
-- statement:
--   The P2 M Eden radius Sq  evolution 4de951b85a7e construction uses the P2 M Eden radius Sq  evolution 4de951b85a7e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InvariantSets.lean#L30-L32
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InvariantSets.lean#L30-L32

import Definitions.Def_Eden_RadialDynamics
import Definitions.Def_Eden_Evolution
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Definitions.Def_Eden_InvariantSets
set_option autoImplicit true
noncomputable section
open Eden

theorem P2M_Eden_radiusSq__evolution_4de951b85a7e (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace) :
    radiusSq₁ (evolution c t p) = squaredRadiusEvolution t (radiusSq₁ p) := by sorry

alias «Eden».«radiusSq₁_evolution» := P2M_Eden_radiusSq__evolution_4de951b85a7e
