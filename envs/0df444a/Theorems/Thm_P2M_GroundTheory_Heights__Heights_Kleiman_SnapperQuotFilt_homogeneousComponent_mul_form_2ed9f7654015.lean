-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotFilt_homogeneousComponent_mul_form_2ed9f7654015
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotFilt_homogeneousComponent_mul_form_2ed9f7654015
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:57:45.547946+00:00
-- url     : https://prove2.me/theorems/84187e5d-1508-47d9-93ba-c2adc67bd2e9
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Snapper Quot Filt homogeneous Component mul form 2ed9f7654015: P2 M Ground Theory Heights  Heights Kleiman Snapper Quot Filt homogeneous Component mul form
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Snapper Quot Filt homogeneous Component mul form 2ed9f7654015 construction uses the P2 M Ground Theory Heights  Heights Kleiman Snapper Quot Filt homogeneous Component mul form 2ed9f7654015 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/HomogeneousComponentMulForm.lean#L264-L287
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/HomogeneousComponentMulForm.lean#L264-L287

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotFilt_homogeneousComponent_mul_form_2ed9f7654015 (c h : Poly S N) {d : ℕ} (hh : h.IsHomogeneous d) (n : ℕ) :
    homogeneousComponent n (c * h) = if d ≤ n then homogeneousComponent (n - d) c * h else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SnapperQuotFilt».«homogeneousComponent_mul_form» := P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotFilt_homogeneousComponent_mul_form_2ed9f7654015
