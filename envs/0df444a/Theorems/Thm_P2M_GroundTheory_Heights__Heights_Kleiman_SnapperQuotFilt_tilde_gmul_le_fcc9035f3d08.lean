-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotFilt_tilde_gmul_le_fcc9035f3d08
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotFilt_tilde_gmul_le_fcc9035f3d08
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:31:05.27917+00:00
-- url     : https://prove2.me/theorems/991f27a5-ac8c-533a-9041-f2c4c0377282
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Snapper Quot Filt tilde gmul le fcc9035f3d08: P2 M Ground Theory Heights  Heights Kleiman Snapper Quot Filt tilde gmul le fcc9035f3d08
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Snapper Quot Filt tilde gmul le fcc9035f3d08 construction uses the P2 M Ground Theory Heights  Heights Kleiman Snapper Quot Filt tilde gmul le fcc9035f3d08 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/HomogeneousComponentMulForm.lean#L310-L338
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/HomogeneousComponentMulForm.lean#L310-L338

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotFilt_tilde_gmul_le_fcc9035f3d08 (M : FinGradedSub (S := S) (x := x) E) {s : ℕ} (h : Fin s → Poly S N) (d : Fin s → ℕ)
    (hh : ∀ l, (h l).IsHomogeneous (d l)) {J : Ideal (Poly S N)} (hJ : ∀ l, h l ∈ J) (F : SubSystem S x E)
    (hF : ∀ I, M.tilde 0 I ≤ F.sub I) (I : Chart x) :
    (gmul M h d).tilde 0 I ≤ (F.twist (idealSys x J)).sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SnapperQuotFilt».«tilde_gmul_le» := P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotFilt_tilde_gmul_le_fcc9035f3d08
