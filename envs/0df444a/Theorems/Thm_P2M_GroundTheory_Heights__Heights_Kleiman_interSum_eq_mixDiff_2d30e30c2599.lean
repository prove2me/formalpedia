-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_interSum_eq_mixDiff_2d30e30c2599
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_interSum_eq_mixDiff_2d30e30c2599
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T07:23:58.610937+00:00
-- url     : https://prove2.me/theorems/4901f650-29a5-4a25-955a-fb0295d5ca3a
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman inter Sum eq mix Diff 2d30e30c2599: P2 M Ground Theory Heights  Heights Kleiman inter Sum eq mix Diff 2d30e30c2599
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman inter Sum eq mix Diff 2d30e30c2599 construction uses the P2 M Ground Theory Heights  Heights Kleiman inter Sum eq mix Diff 2d30e30c2599 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PInterNumAdditive.lean#L114-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PInterNumAdditive.lean#L114-L117

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_interSum_eq_mixDiff_2d30e30c2599 (pp : Ideal (Poly S N)) {n : ℕ} (L : Fin n → SubSystem S x Ω) (c : ℕ) :
    interSum pp L c = mixDiff (fun F => restrLen pp (F.twist (twistSys S x (c : ℤ)))) L := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«interSum_eq_mixDiff» := P2M_GroundTheory_Heights__Heights_Kleiman_interSum_eq_mixDiff_2d30e30c2599
