-- Prove2me | Theorems.Thm_PI_UnitaryCorollaryDerivatives_pb_sum
-- name    : PI.UnitaryCorollaryDerivatives.pb_sum
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:47:00.328567+00:00
-- url     : https://prove2.me/theorems/0896f169-5ca9-5fb3-b92c-a396d68ffc2e
-- title:
--   Unitary Corollary Derivatives: pb sum
-- statement:
--   The Unitary Corollary Derivatives construction uses the pb sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/PolyBB.lean#L166-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/PolyBB.lean#L166-L179

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_PolyBA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_PolyBB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate
noncomputable section
open PI PI.UnitaryCorollaryDerivatives
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}

theorem PI.UnitaryCorollaryDerivatives.pb_sum {ι : Type*} (s : Finset ι) {e : ℝ} (F : ι → B.Mat k r → ℂ)
    (hF : ∀ i ∈ s, PG e (F i)) : PG e (fun g => ∑ i ∈ s, F i g) := by sorry
