-- Prove2me | Theorems.Thm_PI_VolStabW_TopoGram_hform_mulVec
-- name    : PI.VolStabW.TopoGram.hform_mulVec
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:53:49.233241+00:00
-- url     : https://prove2.me/theorems/e08e841d-32e8-417b-add4-e3c3bfdf05ca
-- title:
--   Topo Gram: hform mul Vec
-- statement:
--   The Topo Gram construction uses the hform mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/TopoGram.lean#L16-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/TopoGram.lean#L16-L22

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_NuInvLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TopoGram
import Theorems.Thm_Formalism_UG_P_hform_mulVec

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

theorem PI.VolStabW.TopoGram.hform_mulVec (σ : A →+* A) (J G : Matrix n n A) (x y : n → A) :
    Formalism.UG.hform σ J (G *ᵥ x) (G *ᵥ y) = Formalism.UG.hform σ (Formalism.UG.cT σ G * J * G) x y := by sorry
