-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_exists_generator_at_5bc7d5d10cbc
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_exists_generator_at_5bc7d5d10cbc
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:32:32.761116+00:00
-- url     : https://prove2.me/theorems/d0024264-a6a1-47c3-a667-bcde2d43e905
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman exists generator at 5bc7d5d10cbc: P2 M Ground Theory Heights  Heights Kleiman exists generator at 5bc7d5d10cbc
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman exists generator at 5bc7d5d10cbc construction uses the P2 M Ground Theory Heights  Heights Kleiman exists generator at 5bc7d5d10cbc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PPrimeFiltrationRestrict.lean#L149-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PPrimeFiltrationRestrict.lean#L149-L166

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationRestrict
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
  {x : Fin (N + 1) → Ω} {j : Fin (N + 1)} (hj : x j ≠ 0)
  {K' : Type w} [Field K'] [Algebra S K'] (ψ : chartRing S x (singleChart hj) →ₐ[S] K')
variable (hxy : ∀ i, ψ (ratio hj i) ≠ 0 → x i ≠ 0)

theorem P2M_GroundTheory_Heights__Heights_Kleiman_exists_generator_at_5bc7d5d10cbc {Q0 Q1 : Submodule (chartRing S x (singleChart hj)) Ω} (h : Q0 * Q1 = 1) :
    ∃ q0 ∈ Q0, ∃ q1 ∈ Q1, ∃ c0 : chartRing S x (singleChart hj), (c0 : Ω) = q0 * q1 ∧ ψ c0 ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«exists_generator_at» := P2M_GroundTheory_Heights__Heights_Kleiman_exists_generator_at_5bc7d5d10cbc
