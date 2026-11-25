-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrictGenerated_r_sub_c165d8124f4e
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_RestrictGenerated_r_sub_c165d8124f4e
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:04:40.69825+00:00
-- url     : https://prove2.me/theorems/2ecbb9bb-a4b4-5e22-bc32-32729f1bcd31
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Restrict Generated r sub c165d8124f4e: P2 M Ground Theory Heights  Heights Kleiman Restrict Generated r sub c165d8124f4e
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Restrict Generated r sub c165d8124f4e construction uses the P2 M Ground Theory Heights  Heights Kleiman Restrict Generated r sub c165d8124f4e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrictGenerated.lean#L34-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrictGenerated.lean#L34-L40

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_RestrictGenerated_r_sub_c165d8124f4e {Q : SubSystem S x Ω} {Q' : SubSystem S y K'} {r : Ω → K'}
    (h : RestrictData Q hxy Q' r) (J : Chart y) {u v : Ω}
    (hu : u ∈ Q.sub (liftChart hxy J)) (hv : v ∈ Q.sub (liftChart hxy J)) :
    r (u - v) = r u - r v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«RestrictGenerated».«r_sub» := P2M_GroundTheory_Heights__Heights_Kleiman_RestrictGenerated_r_sub_c165d8124f4e
