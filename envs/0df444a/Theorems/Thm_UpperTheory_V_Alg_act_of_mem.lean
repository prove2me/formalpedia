-- Prove2me | Theorems.Thm_UpperTheory_V_Alg_act_of_mem
-- name    : UpperTheory.V.Alg.act_of_mem
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:40:43.849737+00:00
-- url     : https://prove2.me/theorems/2ae9d281-08d1-48c4-a1da-4b90995a4de8
-- title:
--   Alg: act of mem
-- statement:
--   The Alg construction uses the act of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/CommutativeAlgebra/ResMapBijective.lean#L222-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/CommutativeAlgebra/ResMapBijective.lean#L222-L227

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_CommutativeAlgebra_ResMapBijective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsLocalRing MvPowerSeries
open UpperTheory UpperTheory.V UpperTheory.V.Alg
attribute [instance] IsCO.complete IsCO.isLocalHom
attribute [instance] WPres.fin
variable {O A X K : Type} [CommRing O] [CommRing A] [Algebra O A] [AddCommGroup X] [DecidableEq X]
  (𝒜 : X → Submodule O A) [GradedAlgebra 𝒜] [CommRing K] [Algebra O K]

theorem UpperTheory.V.Alg.act_of_mem (t : Multiplicative X →* Kˣ) (ξ : A →ₐ[O] K) {j : X} {f : A} (hf : f ∈ 𝒜 j) :
    act 𝒜 t ξ f = t (Multiplicative.ofAdd j) * ξ f := by sorry
