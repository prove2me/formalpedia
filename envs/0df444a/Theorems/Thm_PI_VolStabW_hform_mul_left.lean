-- Prove2me | Theorems.Thm_PI_VolStabW_hform_mul_left
-- name    : PI.VolStabW.hform_mul_left
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:46:08.403523+00:00
-- url     : https://prove2.me/theorems/f73f4ff0-aee2-438b-9e4f-b3c902346912
-- title:
--   Vol Stab W: hform mul left
-- statement:
--   The Vol Stab W construction uses the hform mul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensHH.lean#L32-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensHH.lean#L32-L45

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensVDx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHH
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW
  Matrix
variable {A : Type} [CommRing A] (s : A →+* A)

theorem PI.VolStabW.hform_mul_left {M a : ℕ} (Jm : Matrix (Fin M) (Fin M) A) (Y : Fin a → Fin M → A)
    (C : Matrix (Fin a) (Fin a) A) (i j : Fin a) :
    Formalism.UG.hform s Jm (fun l => ∑ k, C i k * Y k l) (Y j) =
      ∑ k, s (C i k) * Formalism.UG.hform s Jm (Y k) (Y j) := by sorry
