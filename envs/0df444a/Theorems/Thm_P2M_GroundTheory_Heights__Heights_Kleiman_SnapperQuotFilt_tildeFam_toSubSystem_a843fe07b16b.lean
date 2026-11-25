-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotFilt_tildeFam_toSubSystem_a843fe07b16b
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotFilt_tildeFam_toSubSystem_a843fe07b16b
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:30:37.433548+00:00
-- url     : https://prove2.me/theorems/bfd27fc0-652a-5d2b-a376-4582f939995b
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Snapper Quot Filt tilde Fam to Sub System a843fe07b16b: P2 M Ground Theory Heights  Heights Kleiman Snapper Quot Filt tilde Fam to Sub System a843fe07b16b
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Snapper Quot Filt tilde Fam to Sub System a843fe07b16b construction uses the P2 M Ground Theory Heights  Heights Kleiman Snapper Quot Filt tilde Fam to Sub System a843fe07b16b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/HomogeneousComponentMulForm.lean#L145-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/HomogeneousComponentMulForm.lean#L145-L146

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
omit [IsScalarTower S Ω E]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotFilt_tildeFam_toSubSystem_a843fe07b16b (M : FinGradedSub (S := S) (x := x) E) :
    (tildeFam M).toSubSystem = M.tildeSys 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SnapperQuotFilt».«tildeFam_toSubSystem» := P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotFilt_tildeFam_toSubSystem_a843fe07b16b
