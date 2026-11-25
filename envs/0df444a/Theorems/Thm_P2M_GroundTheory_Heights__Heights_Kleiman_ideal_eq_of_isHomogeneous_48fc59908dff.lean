-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_ideal_eq_of_isHomogeneous_48fc59908dff
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_ideal_eq_of_isHomogeneous_48fc59908dff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:28:19.606059+00:00
-- url     : https://prove2.me/theorems/e7d4b5e4-7fba-4e8b-839d-b66f6589b033
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman ideal eq of is Homogeneous 48fc59908dff: P2 M Ground Theory Heights  Heights Kleiman ideal eq of is Homogeneous 48fc59908dff
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman ideal eq of is Homogeneous 48fc59908dff construction uses the P2 M Ground Theory Heights  Heights Kleiman ideal eq of is Homogeneous 48fc59908dff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PPrimeFiltrationPoint.lean#L38-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PPrimeFiltrationPoint.lean#L38-L49

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {j : Fin (N + 1)}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_ideal_eq_of_isHomogeneous_48fc59908dff {I J : Ideal (Poly S N)}
    (hI : ∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I)
    (hJ : ∀ p ∈ J, ∀ d : ℕ, homogeneousComponent d p ∈ J)
    (h : ∀ (f : Poly S N) (e : ℕ), f.IsHomogeneous e → (f ∈ I ↔ f ∈ J)) : I = J := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«ideal_eq_of_isHomogeneous» := P2M_GroundTheory_Heights__Heights_Kleiman_ideal_eq_of_isHomogeneous_48fc59908dff
