-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_specRest_map_1f6b35ea43b2
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_specRest_map_1f6b35ea43b2
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:43:59.226307+00:00
-- url     : https://prove2.me/theorems/7cb3fd6f-6a2b-4090-9d51-6a13ed8e18af
-- title:
--   P2 M Ground Theory Heights  Heights Vertical spec Rest map 1f6b35ea43b2: P2 M Ground Theory Heights  Heights Vertical spec Rest map 1f6b35ea43b2
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical spec Rest map 1f6b35ea43b2 construction uses the P2 M Ground Theory Heights  Heights Vertical spec Rest map 1f6b35ea43b2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PChowNormForm.lean#L11-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PChowNormForm.lean#L11-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PChowNormForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Vertical_specRest_map_1f6b35ea43b2 {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] {n e : ℕ}
    (φ : R →+* S) (ψ : S →+* T) (f : MvPolynomial (Fin (e + 1) × Fin n) R) (y : Par e n → S) :
    (specRest φ f y).map ψ = specRest (ψ.comp φ) f (ψ ∘ y) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«specRest_map» := P2M_GroundTheory_Heights__Heights_Vertical_specRest_map_1f6b35ea43b2
