-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_h_add_left
-- name    : PI.VolSemiDirect.W.PG.Dat.h_add_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:18:17.436321+00:00
-- url     : https://prove2.me/theorems/ae61ff27-8723-4b8e-ac75-bf9a24ba2836
-- title:
--   Dat: h add left
-- statement:
--   The Dat construction uses the h add left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/ProjGen.lean#L52-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/ProjGen.lean#L52-L53

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W PI.VolSemiDirect.W.PG
open Formalism.UG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
open PI.VolSemiDirect.W.PG.Dat
variable (D : Dat A n r)

theorem PI.VolSemiDirect.W.PG.Dat.h_add_left (x x' y : n → A) : D.h (x + x') y = D.h x y + D.h x' y := by sorry
