-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_GenChowIrreducible_map_specRest_1008735764af
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_GenChowIrreducible_map_specRest_1008735764af
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:42:09.546714+00:00
-- url     : https://prove2.me/theorems/29ef88da-1474-50f4-ad6e-0bd36d241ae4
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Gen Chow Irreducible map spec Rest 1008735764af: P2 M Ground Theory Heights  Heights Vertical Gen Chow Irreducible map spec Rest 1008735764af
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Gen Chow Irreducible map spec Rest 1008735764af construction uses the P2 M Ground Theory Heights  Heights Vertical Gen Chow Irreducible map spec Rest 1008735764af property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PGenChowIrreducible.lean#L16-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PGenChowIrreducible.lean#L16-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PGenChowIrreducible
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
open GroundTheory.Heights₂.Heights.Vertical.GenChowIrreducible
variable {n e : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Vertical_GenChowIrreducible_map_specRest_1008735764af {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] (φ : R →+* S)
    (ψ : S →+* T) (f : MvPolynomial (Fin (e + 1) × Fin n) R) (y : Par e n → S) :
    (specRest φ f y).map ψ = specRest (ψ.comp φ) f (ψ ∘ y) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«GenChowIrreducible».«map_specRest» := P2M_GroundTheory_Heights__Heights_Vertical_GenChowIrreducible_map_specRest_1008735764af
