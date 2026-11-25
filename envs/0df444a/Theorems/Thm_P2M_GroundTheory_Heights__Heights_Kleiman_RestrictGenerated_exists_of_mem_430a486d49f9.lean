-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrictGenerated_exists_of_mem_430a486d49f9
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_RestrictGenerated_exists_of_mem_430a486d49f9
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:59:24.126054+00:00
-- url     : https://prove2.me/theorems/12f04d23-b0d0-57e0-98bf-110f3682ab5f
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Restrict Generated exists of mem 430a486d49f9: P2 M Ground Theory Heights  Heights Kleiman Restrict Generated exists of mem 430a486d49f9
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Restrict Generated exists of mem 430a486d49f9 construction uses the P2 M Ground Theory Heights  Heights Kleiman Restrict Generated exists of mem 430a486d49f9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrictGenerated.lean#L42-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrictGenerated.lean#L42-L59

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsRestrictGenerated
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepThreeOnWGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrictGenerated
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
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.RestrictGenerated
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {K' : Type w} [Field K'] [Algebra S K'] {y : Fin (N + 1) → K'}
  {hxy : ∀ i, y i ≠ 0 → x i ≠ 0}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_RestrictGenerated_exists_of_mem_430a486d49f9 {Q : SubSystem S x Ω} {Q' : SubSystem S y K'} {r : Ω → K'}
    (h : RestrictData Q hxy Q' r) (J : Chart y) {t : K'} (ht : t ∈ Q'.sub J) :
    ∃ w ∈ Q.sub (liftChart hxy J), r w = t := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«RestrictGenerated».«exists_of_mem» := P2M_GroundTheory_Heights__Heights_Kleiman_RestrictGenerated_exists_of_mem_430a486d49f9
