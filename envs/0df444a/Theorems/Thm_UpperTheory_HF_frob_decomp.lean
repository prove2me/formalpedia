-- Prove2me | Theorems.Thm_UpperTheory_HF_frob_decomp
-- name    : UpperTheory.HF.frob_decomp
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:23:00.90506+00:00
-- url     : https://prove2.me/theorems/df426f75-4b97-5b7a-a15e-54f28b7fe41c
-- title:
--   HF: frob decomp
-- statement:
--   The HF construction uses the frob decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/FrobDecomp.lean#L9-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/FrobDecomp.lean#L9-L51

import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_SizeDefs
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_FrobGSpec
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_FrobDecomp
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

theorem UpperTheory.HF.frob_decomp :
    ∀ (φ : Frame) (H : HostAx φ) (p : ℕ) [Fact p.Prime], ¬ p ∣ H.condN → ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})],
      (∀ σ : H.E ≃ₐ[ℚ] H.E, σ ∈ MulAction.stabilizer (H.E ≃ₐ[ℚ] H.E) P ↔ H.galE σ ∈ Subgroup.zpowers (H.frobG p)) ∧
      Nat.card (MulAction.stabilizer (H.E ≃ₐ[ℚ] H.E) P) = orderOf (H.frobG p) ∧
      (primesOver (span {(p : ℤ)}) (𝓞 H.E)).ncard * orderOf (H.frobG p) = 4 * φ.ord := by sorry
