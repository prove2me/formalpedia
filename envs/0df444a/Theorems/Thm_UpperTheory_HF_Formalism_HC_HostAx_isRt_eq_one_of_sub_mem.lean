-- Prove2me | Theorems.Thm_UpperTheory_HF_Formalism_HC_HostAx_isRt_eq_one_of_sub_mem
-- name    : UpperTheory.HF.Formalism.HC.HostAx.isRt_eq_one_of_sub_mem
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:13:08.209386+00:00
-- url     : https://prove2.me/theorems/6b29813d-8a07-49e6-85a7-8f542d11cc65
-- title:
--   Host Ax: is Rt eq one of sub mem
-- statement:
--   The Host Ax construction uses the is Rt eq one of sub mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/MuIsRteqoneofsubmem.lean#L25-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/MuIsRteqoneofsubmem.lean#L25-L42

import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_MuDefs
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_MuIsRteqoneofsubmem
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

theorem UpperTheory.HF.Formalism.HC.HostAx.isRt_eq_one_of_sub_mem :
    ∀ {φ : Frame} (H : HostAx φ) (p : ℕ), p.Prime → ¬ p ∣ H.muW → ∀ (P : Ideal (𝓞 H.E)), P.IsPrime → (p : 𝓞 H.E) ∈ P →
      ∀ ξ ξ' : 𝓞 H.E, H.IsRt (ξ : H.E) → H.IsRt (ξ' : H.E) → ξ - ξ' ∈ P → ξ = ξ' := by sorry
