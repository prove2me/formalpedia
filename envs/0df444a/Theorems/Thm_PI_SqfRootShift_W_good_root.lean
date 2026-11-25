-- Prove2me | Theorems.Thm_PI_SqfRootShift_W_good_root
-- name    : PI.SqfRootShift.W.good_root
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:27:19.836987+00:00
-- url     : https://prove2.me/theorems/452ffc3e-3c0f-5ac4-adbd-a97461728c3d
-- title:
--   W: good root
-- statement:
--   The W construction uses the good root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootShift/CountB.lean#L39-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootShift/CountB.lean#L39-L72

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_CountA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_CountB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open PI PI.SqfRootShift PI.SqfRootShift.W
open PI.SqfLab
variable {g : ℕ} [Fact g.Prime]

theorem PI.SqfRootShift.W.good_root (c : (ZMod g)ˣ) (P : (ZMod g)[X]) (hP : Good c P) (z : Fbar g)
    (hz : z ∈ (P.map (algebraMap (ZMod g) (Fbar g))).roots) :
    (z * (algebraMap (ZMod g) (Fbar g) (c : ZMod g))⁻¹) ^ (g ^ P.natDegree - 1) = 1 ∧
      ∃ ℓ, ℓ.Prime ∧ ∃ j, (z * (algebraMap (ZMod g) (Fbar g) (c : ZMod g))⁻¹) ^ (ℓ ^ j) = 1 := by sorry
