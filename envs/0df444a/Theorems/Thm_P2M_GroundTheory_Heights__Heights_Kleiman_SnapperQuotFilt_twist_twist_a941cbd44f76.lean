-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotFilt_twist_twist_a941cbd44f76
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotFilt_twist_twist_a941cbd44f76
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:08:45.290802+00:00
-- url     : https://prove2.me/theorems/38740f39-0dfa-4a7d-857e-f9dcf16022bf
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Snapper Quot Filt twist twist a941cbd44f76: P2 M Ground Theory Heights  Heights Kleiman Snapper Quot Filt twist twist a941cbd44f76
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Snapper Quot Filt twist twist a941cbd44f76 construction uses the P2 M Ground Theory Heights  Heights Kleiman Snapper Quot Filt twist twist a941cbd44f76 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/HomogeneousComponentMulForm.lean#L22-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/HomogeneousComponentMulForm.lean#L22-L52

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotFiltSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PDomination
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_HomogeneousComponentMulForm
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
open GroundTheory.Heights₂.Heights.Kleiman.SnapperQuotFilt
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotFilt_twist_twist_a941cbd44f76 (F : SubSystem S x E) (P Q : SubSystem S x Ω) :
    (F.twist P).twist Q = F.twist (P.twist Q) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SnapperQuotFilt».«twist_twist» := P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotFilt_twist_twist_a941cbd44f76
