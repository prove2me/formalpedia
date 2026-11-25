-- Prove2me | Theorems.Thm_P2M_GlobalTheory_Avoid_pairingDual__Multi_comp_bbdba73fb990
-- name    : P2M_GlobalTheory_Avoid_pairingDual__Multi_comp_bbdba73fb990
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:01:59.241563+00:00
-- url     : https://prove2.me/theorems/bcb340ae-dbc1-4808-a4c7-6e71c88a4527
-- title:
--   P2 M Global Theory Avoid pairing Dual  Multi comp bbdba73fb990: P2 M Global Theory Avoid pairing Dual  Multi comp bbdba73fb990
-- statement:
--   The P2 M Global Theory Avoid pairing Dual  Multi comp bbdba73fb990 construction uses the P2 M Global Theory Avoid pairing Dual  Multi comp bbdba73fb990 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasisMapOfLiftBaseChangeSurjective.lean#L62-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasisMapOfLiftBaseChangeSurjective.lean#L62-L72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasisMapOfLiftBaseChangeSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Function
open scoped TensorProduct Pointwise
open GlobalTheory
open GlobalTheory.Avoid
open exteriorPower

theorem P2M_GlobalTheory_Avoid_pairingDual__Multi_comp_bbdba73fb990 {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {r : ℕ} (φ : M →ₗ[R] N) (f : Fin r → Dual R N)
    (x : ⋀[R]^r M) :
    pairingDual R M r (ιMulti R r fun k => f k ∘ₗ φ) x =
      pairingDual R N r (ιMulti R r f) (exteriorPower.map r φ x) := by sorry

alias «GlobalTheory».«Avoid».«pairingDual_ιMulti_comp» := P2M_GlobalTheory_Avoid_pairingDual__Multi_comp_bbdba73fb990
