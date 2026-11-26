-- Prove2me | Theorems.Thm_P2M_Eden_radiusSq__nonneg_5272e4fb8458
-- name    : P2M_Eden_radiusSq__nonneg_5272e4fb8458
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:11:08.821986+00:00
-- url     : https://prove2.me/theorems/cab64708-792b-48f6-8611-08013ce53d1d
-- title:
--   P2 M Eden radius Sq  nonneg 5272e4fb8458: P2 M Eden radius Sq  nonneg 5272e4fb8458
-- statement:
--   The P2 M Eden radius Sq  nonneg 5272e4fb8458 construction uses the P2 M Eden radius Sq  nonneg 5272e4fb8458 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InvariantSets.lean#L16-L17
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InvariantSets.lean#L16-L17

import Definitions.Def_Eden_RadialDynamics
import Definitions.Def_Eden_Evolution
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Definitions.Def_Eden_InvariantSets
set_option autoImplicit true
noncomputable section
open Eden

theorem P2M_Eden_radiusSq__nonneg_5272e4fb8458 (p : PhaseSpace) : 0 ≤ radiusSq₁ p := by sorry

alias «Eden».«radiusSq₁_nonneg» := P2M_Eden_radiusSq__nonneg_5272e4fb8458
