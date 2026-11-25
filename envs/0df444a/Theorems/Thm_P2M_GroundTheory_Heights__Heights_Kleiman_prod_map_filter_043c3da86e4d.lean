-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_prod_map_filter_043c3da86e4d
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_prod_map_filter_043c3da86e4d
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:04:21.879348+00:00
-- url     : https://prove2.me/theorems/effc98ba-7dbe-4d39-84ef-8e7736bac916
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman prod map filter 043c3da86e4d: P2 M Ground Theory Heights  Heights Kleiman prod map filter 043c3da86e4d
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman prod map filter 043c3da86e4d construction uses the P2 M Ground Theory Heights  Heights Kleiman prod map filter 043c3da86e4d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PInterNumAdditive.lean#L39-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PInterNumAdditive.lean#L39-L46

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_prod_map_filter_043c3da86e4d {α M : Type*} [CommMonoid M] (p : α → Bool) (f : α → M) (l : List α) :
    ((l.filter p).map f).prod = (l.map fun a => if p a then f a else 1).prod := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«prod_map_filter» := P2M_GroundTheory_Heights__Heights_Kleiman_prod_map_filter_043c3da86e4d
