-- Prove2me | Theorems.Thm_UpperTheory_V_Hi_Frame_ra_apply
-- name    : UpperTheory.V.Hi.Frame.ra_apply
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:40:44.153426+00:00
-- url     : https://prove2.me/theorems/ecad5c8c-afaa-4af2-a4ca-83f94cc58fec
-- title:
--   Frame: ra apply
-- statement:
--   The Frame construction uses the ra apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/HeckeAlgebras/ContinuousTorusCharacter.lean#L188-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/HeckeAlgebras/ContinuousTorusCharacter.lean#L188-L189

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_FixedSubgroup
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_HeckeAlgebras_ContinuousTorusCharacter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsLocalRing Matrix
open UpperTheory UpperTheory.V UpperTheory.V.Hi
attribute [instance] IsCNL.complete IsCNL.finite
open UpperTheory.V.Hi.Frame
variable {Γ Ga Gp : Type} [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp)
variable {A : Type} [CommRing A] {m : ℕ} (τ : X.Ub →* GL (Fin m) A) (θ : X.I.T →* Aˣ)

theorem UpperTheory.V.Hi.Frame.ra_apply (u : X.Ub) (f : X.Fn A m) (g : Ga × Gp) :
    X.ra τ u f g = (τ u : Matrix (Fin m) (Fin m) A) *ᵥ f (g * ((u : Ga), 1)) := by sorry
