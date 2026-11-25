-- Prove2me | Theorems.Thm_UpperTheory_Mu_splitNotDvd
-- name    : UpperTheory.Mu.splitNotDvd
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:13:19.856325+00:00
-- url     : https://prove2.me/theorems/b9aa681a-8a6b-4be7-bac5-092712b9732a
-- title:
--   Mu: split Not Dvd
-- statement:
--   The Mu construction uses the split Not Dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RootsOfUnity/SplitNotDvd.lean#L7-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RootsOfUnity/SplitNotDvd.lean#L7-L65

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_ExistsPrimitiveRootTorsionOrder
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RootsOfUnity_SplitNotDvd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.HC
open Ideal

theorem UpperTheory.Mu.splitNotDvd :
    ∀ (φ : Frame) (H : HostAx φ), H.toHostRaw.Exact → ∀ p : ℕ, p.Prime → {v : HeightOneSpectrum (𝓞 H.E) | ((p : ℕ) : 𝓞 H.E) ∈ v.asIdeal}.ncard = Module.finrank ℚ H.E → ¬ p ∣ H.QS := by sorry
