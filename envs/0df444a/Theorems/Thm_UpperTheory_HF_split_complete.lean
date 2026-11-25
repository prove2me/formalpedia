-- Prove2me | Theorems.Thm_UpperTheory_HF_split_complete
-- name    : UpperTheory.HF.split_complete
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:13:23.782489+00:00
-- url     : https://prove2.me/theorems/9ec9b497-41b3-4bac-b7fc-cff6062c4eb1
-- title:
--   HF: split complete
-- statement:
--   The HF construction uses the split complete property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/splitComplete.lean#L10-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/splitComplete.lean#L10-L40

import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_SizeDefs
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_FrobGSpec
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_FrobDecomp
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_splitComplete
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory.HF
open NumberField IntermediateField Ideal Formalism.FrobeniusOrbits Formalism.HC
open scoped Pointwise

theorem UpperTheory.HF.split_complete :
    ∀ (φ : Frame) (H : HostAx φ) (p : ℕ), p.Prime → p ≡ 1 [MOD H.condN] →
      ¬ p ∣ H.condN ∧ H.frobG p = 1 ∧ jacobiSym (-(H.d : ℤ)) p = 1 ∧ H.condN < p ∧ 16 * H.d * H.q ∣ p - 1 ∧
      (primesOver (span {(p : ℤ)}) (𝓞 H.E)).ncard = 4 * φ.ord := by sorry
