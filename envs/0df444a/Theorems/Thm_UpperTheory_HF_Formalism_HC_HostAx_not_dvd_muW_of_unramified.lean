-- Prove2me | Theorems.Thm_UpperTheory_HF_Formalism_HC_HostAx_not_dvd_muW_of_unramified
-- name    : UpperTheory.HF.Formalism.HC.HostAx.not_dvd_muW_of_unramified
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:20:39.505117+00:00
-- url     : https://prove2.me/theorems/eb985cd5-f153-54cb-9321-a0ff79f0524c
-- title:
--   Host Ax: not dvd mu W of unramified
-- statement:
--   The Host Ax construction uses the not dvd mu W of unramified property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/MuNotdvdmuWofunramified.lean#L21-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/MuNotdvdmuWofunramified.lean#L21-L30

import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_MuDefs
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_MuNotdvdmuWofunramified
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory.HF
open NumberField IntermediateField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

theorem UpperTheory.HF.Formalism.HC.HostAx.not_dvd_muW_of_unramified :
    ∀ {φ : Frame} (H : HostAx φ) (p : ℕ), p.Prime → p ≠ 2 → ∀ (P : Ideal (𝓞 H.E)), P.IsPrime → (p : 𝓞 H.E) ∈ P → (p : 𝓞 H.E) ∉ P ^ 2 → ¬ p ∣ H.muW := by sorry
