-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_DimTie_trdeg_range_544901a4c07b
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_DimTie_trdeg_range_544901a4c07b
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:58:44.910347+00:00
-- url     : https://prove2.me/theorems/35fe3710-8c6c-4ed3-a9b9-7fb467cc2f24
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Dim Tie trdeg range 544901a4c07b: P2 M Ground Theory Heights  Heights Kleiman Dim Tie trdeg range 544901a4c07b
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Dim Tie trdeg range 544901a4c07b construction uses the P2 M Ground Theory Heights  Heights Kleiman Dim Tie trdeg range 544901a4c07b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PDimTie.lean#L130-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PDimTie.lean#L130-L142

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PDimTie
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
open MvPolynomial Algebra Cardinal
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.DimTie
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
variable (y : Fin (N + 1) → Ω) {i₀ : Fin (N + 1)} (hi₀ : y i₀ ≠ 0)

theorem P2M_GroundTheory_Heights__Heights_Kleiman_DimTie_trdeg_range_544901a4c07b :
    trdeg k (dehom (k := k) y hi₀).range = trdeg k (ratioRing (k := k) y) + 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«DimTie».«trdeg_range» := P2M_GroundTheory_Heights__Heights_Kleiman_DimTie_trdeg_range_544901a4c07b
