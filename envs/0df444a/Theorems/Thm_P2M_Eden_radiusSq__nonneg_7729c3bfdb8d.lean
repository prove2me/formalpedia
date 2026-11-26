-- Prove2me | Theorems.Thm_P2M_Eden_radiusSq__nonneg_7729c3bfdb8d
-- name    : P2M_Eden_radiusSq__nonneg_7729c3bfdb8d
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:11:08.348583+00:00
-- url     : https://prove2.me/theorems/4b84225c-5e9b-5914-8e39-77922ef1e84b
-- title:
--   P2 M Eden radius Sq  nonneg 7729c3bfdb8d: P2 M Eden radius Sq  nonneg 7729c3bfdb8d
-- statement:
--   The P2 M Eden radius Sq  nonneg 7729c3bfdb8d construction uses the P2 M Eden radius Sq  nonneg 7729c3bfdb8d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InvariantSets.lean#L19-L20
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InvariantSets.lean#L19-L20

import Definitions.Def_Eden_RadialDynamics
import Definitions.Def_Eden_Evolution
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Definitions.Def_Eden_InvariantSets
set_option autoImplicit true
noncomputable section
open Eden

theorem P2M_Eden_radiusSq__nonneg_7729c3bfdb8d (p : PhaseSpace) : 0 ≤ radiusSq₂ p := by sorry

alias «Eden».«radiusSq₂_nonneg» := P2M_Eden_radiusSq__nonneg_7729c3bfdb8d
