-- Prove2me | Theorems.Thm_UpperTheory_rootOfUnity_galois_action_CMDatum
-- name    : UpperTheory.rootOfUnity_galois_action_CMDatum
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T19:25:48.37412+00:00
-- url     : https://prove2.me/theorems/6656e8f2-c71b-4a06-825d-7bcb7a9ced17
-- title:
--   Upper Theory: root Of Unity galois action CMDatum
-- statement:
--   The Upper Theory construction uses the root Of Unity galois action CMDatum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/WeightCongruences/RootOfUnityGaloisActionCMDatum.lean#L7-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/WeightCongruences/RootOfUnityGaloisActionCMDatum.lean#L7-L18

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcEqOfPowEqOne
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_RootOfUnityGaloisActionCMDatum
import Theorems.Thm_Formalism_FrobeniusOrbits_Final_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HC

theorem UpperTheory.rootOfUnity_galois_action_CMDatum :
    ∀ (φ : Frame) (H : HostAx φ) (z : H.E), (∃ m : ℕ, 0 < m ∧ z ^ m = 1) →
      H.gal.symm φ.iod z = z ∧ H.conj z = z⁻¹ ∧ H.gal.symm φ.sg z = z⁻¹ := by sorry
