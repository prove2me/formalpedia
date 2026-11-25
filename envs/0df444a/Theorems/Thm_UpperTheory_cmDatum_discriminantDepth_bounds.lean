-- Prove2me | Theorems.Thm_UpperTheory_cmDatum_discriminantDepth_bounds
-- name    : UpperTheory.cmDatum_discriminantDepth_bounds
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T01:04:21.110327+00:00
-- url     : https://prove2.me/theorems/3bf9281f-d484-43fb-974c-2e30081969bc
-- title:
--   Upper Theory: cm Datum discriminant Depth bounds
-- statement:
--   The Upper Theory construction uses the cm Datum discriminant Depth bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CMTraceForms/CmDatumDiscriminantDepthBounds.lean#L12-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CMTraceForms/CmDatumDiscriminantDepthBounds.lean#L12-L40

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_SlopeTestRemainingChoices
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_VdLe
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_inertQ
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_InertD
import Definitions.Def_Development_AutomorphicArithmetic_CMTraceForms_CmDatumDiscriminantDepthBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory.HF
open NumberField Formalism.HC

theorem UpperTheory.cmDatum_discriminantDepth_bounds :
    ∀ {φ : Frame} (H : HostAx φ), (∀ l ∈ H.small, H.vdH l ≤ (padicValNat l H.QS : ℝ) ∧ (padicValNat l H.QS : ℝ) ≤ Real.logb 2 H.QS) ∧
      H.vdH H.q ≤ 1 / 2 ∧ H.vdH H.d ≤ 1 / 2 ∧ 0 ≤ Real.logb 2 H.QS ∧
      ∀ p : ℕ, H.vdH p = (padicValInt p (discr H.E) : ℝ) / (Module.finrank ℚ H.E : ℝ) := by sorry
