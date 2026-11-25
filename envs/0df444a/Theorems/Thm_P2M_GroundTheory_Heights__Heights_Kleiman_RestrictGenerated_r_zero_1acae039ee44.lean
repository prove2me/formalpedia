-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrictGenerated_r_zero_1acae039ee44
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_RestrictGenerated_r_zero_1acae039ee44
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:17:06.465499+00:00
-- url     : https://prove2.me/theorems/ec8d4cf5-ef0e-5ae3-b2f3-7624291f592c
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Restrict Generated r zero 1acae039ee44: P2 M Ground Theory Heights  Heights Kleiman Restrict Generated r zero 1acae039ee44
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Restrict Generated r zero 1acae039ee44 construction uses the P2 M Ground Theory Heights  Heights Kleiman Restrict Generated r zero 1acae039ee44 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrictGenerated.lean#L28-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrictGenerated.lean#L28-L32

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_RestrictGenerated_r_zero_1acae039ee44 {Q : SubSystem S x Ω} {Q' : SubSystem S y K'} {r : Ω → K'}
    (h : RestrictData Q hxy Q' r) (J : Chart y) : r 0 = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«RestrictGenerated».«r_zero» := P2M_GroundTheory_Heights__Heights_Kleiman_RestrictGenerated_r_zero_1acae039ee44
