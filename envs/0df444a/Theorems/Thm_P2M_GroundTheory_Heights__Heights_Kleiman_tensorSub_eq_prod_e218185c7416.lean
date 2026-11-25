-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_tensorSub_eq_prod_e218185c7416
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_tensorSub_eq_prod_e218185c7416
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:23:16.394873+00:00
-- url     : https://prove2.me/theorems/018ad36b-dd79-599c-b56b-46bdbe37dba1
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman tensor Sub eq prod e218185c7416: P2 M Ground Theory Heights  Heights Kleiman tensor Sub eq prod e218185c7416
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman tensor Sub eq prod e218185c7416 construction uses the P2 M Ground Theory Heights  Heights Kleiman tensor Sub eq prod e218185c7416 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PInterNumAdditive.lean#L48-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PInterNumAdditive.lean#L48-L56

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_tensorSub_eq_prod_e218185c7416 {n : ℕ} (L : Fin n → SubSystem S x Ω) (T : Finset (Fin n)) :
    tensorSub L T = ∏ j ∈ T, L j := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«tensorSub_eq_prod» := P2M_GroundTheory_Heights__Heights_Kleiman_tensorSub_eq_prod_e218185c7416
