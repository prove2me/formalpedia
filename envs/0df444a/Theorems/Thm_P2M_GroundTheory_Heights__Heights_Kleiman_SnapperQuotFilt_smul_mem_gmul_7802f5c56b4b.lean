-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotFilt_smul_mem_gmul_7802f5c56b4b
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotFilt_smul_mem_gmul_7802f5c56b4b
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:28:13.081781+00:00
-- url     : https://prove2.me/theorems/7becfd18-c3be-4fa5-9e4c-3639074da1c9
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Snapper Quot Filt smul mem gmul 7802f5c56b4b: P2 M Ground Theory Heights  Heights Kleiman Snapper Quot Filt smul mem gmul 7802f5c56b4b
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Snapper Quot Filt smul mem gmul 7802f5c56b4b construction uses the P2 M Ground Theory Heights  Heights Kleiman Snapper Quot Filt smul mem gmul 7802f5c56b4b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/HomogeneousComponentMulForm.lean#L289-L308
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/HomogeneousComponentMulForm.lean#L289-L308

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotFilt_smul_mem_gmul_7802f5c56b4b (M : FinGradedSub (S := S) (x := x) E) {s : ℕ} (h : Fin s → Poly S N) (d : Fin s → ℕ)
    (hh : ∀ l, (h l).IsHomogeneous (d l)) {J : Ideal (Poly S N)} (hJ : Ideal.span (Set.range h) = J)
    {f : Poly S N} {e : ℕ} (hfJ : f ∈ J) (hf : f.IsHomogeneous e) {a : ℤ} {z : E} (hz : z ∈ M.piece a) :
    aeval x f • z ∈ (gmul M h d).piece (a + e) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SnapperQuotFilt».«smul_mem_gmul» := P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotFilt_smul_mem_gmul_7802f5c56b4b
