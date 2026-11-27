-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotFilt_le_of_forms_8d90d8ecdbb7
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotFilt_le_of_forms_8d90d8ecdbb7
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:30:21.4908+00:00
-- url     : https://prove2.me/theorems/0c19d177-7c32-5b09-8fff-799c04ce7ccb
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Snapper Quot Filt le of forms 8d90d8ecdbb7: P2 M Ground Theory Heights  Heights Kleiman Snapper Quot Filt le of forms 8d90d8ecdbb7
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Snapper Quot Filt le of forms 8d90d8ecdbb7 construction uses the P2 M Ground Theory Heights  Heights Kleiman Snapper Quot Filt le of forms 8d90d8ecdbb7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/HomogeneousComponentMulForm.lean#L340-L343
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/HomogeneousComponentMulForm.lean#L340-L343

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotFilt_le_of_forms_8d90d8ecdbb7 {J P : Ideal (Poly S N)} (hJ : ∀ f ∈ J, ∀ d : ℕ, homogeneousComponent d f ∈ J)
    (h : ∀ (f : Poly S N) (e : ℕ), f ∈ J → f.IsHomogeneous e → f ∈ P) : J ≤ P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SnapperQuotFilt».«le_of_forms» := P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotFilt_le_of_forms_8d90d8ecdbb7
