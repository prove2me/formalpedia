-- Prove2me | Theorems.Thm_PI_VolStabW_TopoGram_hform_eq
-- name    : PI.VolStabW.TopoGram.hform_eq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:40:33.775071+00:00
-- url     : https://prove2.me/theorems/ab5ea2ad-4d3d-4d02-9b98-9b48caa392c7
-- title:
--   Topo Gram: hform eq
-- statement:
--   The Topo Gram construction uses the hform eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/TopoGram.lean#L12-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/TopoGram.lean#L12-L14

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_NuInvLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TopoGram
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.TopoGram
open Matrix
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem PI.VolStabW.TopoGram.hform_eq (σ : A →+* A) (J : Matrix n n A) (x y : n → A) :
    Formalism.UG.hform σ J x y = (fun i => σ (x i)) ⬝ᵥ (J *ᵥ y) := by sorry
