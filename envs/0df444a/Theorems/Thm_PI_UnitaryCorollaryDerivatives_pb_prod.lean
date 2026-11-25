-- Prove2me | Theorems.Thm_PI_UnitaryCorollaryDerivatives_pb_prod
-- name    : PI.UnitaryCorollaryDerivatives.pb_prod
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:34:35.893946+00:00
-- url     : https://prove2.me/theorems/fbd1c2d4-6366-4889-8a66-b4771e0c2bed
-- title:
--   Unitary Corollary Derivatives: pb prod
-- statement:
--   The Unitary Corollary Derivatives construction uses the pb prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/PolyBB.lean#L150-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/PolyBB.lean#L150-L164

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

theorem PI.UnitaryCorollaryDerivatives.pb_prod {ι : Type*} (s : Finset ι) (e : ι → ℝ) (F : ι → B.Mat k r → ℂ)
    (hF : ∀ i ∈ s, PG (e i) (F i)) : PG (∑ i ∈ s, e i) (fun g => ∏ i ∈ s, F i g) := by sorry
