-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_foldl_twist_eq_mul_3a1641a715cf
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_foldl_twist_eq_mul_3a1641a715cf
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:12:20.190054+00:00
-- url     : https://prove2.me/theorems/d05f5af8-4b4b-5245-a13b-e71a9152d9f0
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman foldl twist eq mul 3a1641a715cf: P2 M Ground Theory Heights  Heights Kleiman foldl twist eq mul 3a1641a715cf
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman foldl twist eq mul 3a1641a715cf construction uses the P2 M Ground Theory Heights  Heights Kleiman foldl twist eq mul 3a1641a715cf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PInterNumAdditive.lean#L31-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PInterNumAdditive.lean#L31-L37

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StInterNumAdditive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StInterNumEventual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StInterSumTopVanish
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_InterSumEventuallyEqInterNum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PInterNumAdditive
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
open MvPolynomial Filter
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
attribute [local instance] twistMonoid

theorem P2M_GroundTheory_Heights__Heights_Kleiman_foldl_twist_eq_mul_3a1641a715cf {n : ℕ} (L : Fin n → SubSystem S x Ω) (l : List (Fin n)) (F : SubSystem S x Ω) :
    l.foldl (fun F i => F.twist (L i)) F = F * (l.map L).prod := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«foldl_twist_eq_mul» := P2M_GroundTheory_Heights__Heights_Kleiman_foldl_twist_eq_mul_3a1641a715cf
