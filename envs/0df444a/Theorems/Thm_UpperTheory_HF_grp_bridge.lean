-- Prove2me | Theorems.Thm_UpperTheory_HF_grp_bridge
-- name    : UpperTheory.HF.grp_bridge
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:23:01.147039+00:00
-- url     : https://prove2.me/theorems/f73e41ec-bd01-5975-b818-743616ec9334
-- title:
--   HF: grp bridge
-- statement:
--   The HF construction uses the grp bridge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/GrpBridge.lean#L13-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/GrpBridge.lean#L13-L42

import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiffDefs
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_ArtLSpec
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_GrpBridge
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory.HF
open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

theorem UpperTheory.HF.grp_bridge :
    ∀ {φ : Frame} (H : HostAx φ) {l : ℕ}, l.Prime → ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})], (∀ σ : H.E ≃ₐ[ℚ] H.E, (∀ x : 𝓞 H.E, σ • x - x ∈ P) ↔ H.gal σ ∈ H.inertG l) ∧ (∀ σ : H.E ≃ₐ[ℚ] H.E, σ ∈ MulAction.stabilizer _ P ↔ H.gal σ ∈ H.decG l) ∧ P.ramificationIdx ℤ = H.el l ∧ P.inertiaDeg ℤ = H.nw l ∧ Nat.card (H.decG l) = H.el l * H.nw l ∧ (primesOver (span {(l : ℤ)}) (𝓞 H.E)).ncard * (H.el l * H.nw l) = 4 * φ.ord := by sorry
