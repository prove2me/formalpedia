-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_DimTie_trdeg_polynomial_a210957d600c
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_DimTie_trdeg_polynomial_a210957d600c
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:56:02.064027+00:00
-- url     : https://prove2.me/theorems/29387f24-0b15-4c93-907c-ee3b7587ddb1
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Dim Tie trdeg polynomial a210957d600c: P2 M Ground Theory Heights  Heights Kleiman Dim Tie trdeg polynomial a210957d600c
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Dim Tie trdeg polynomial a210957d600c construction uses the P2 M Ground Theory Heights  Heights Kleiman Dim Tie trdeg polynomial a210957d600c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PDimTie.lean#L37-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PDimTie.lean#L37-L41

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_DimTie_trdeg_polynomial_a210957d600c (D : Type w) [CommRing D] [IsDomain D] [Algebra k D] [FaithfulSMul k D] :
    trdeg k (Polynomial D) = trdeg k D + 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«DimTie».«trdeg_polynomial» := P2M_GroundTheory_Heights__Heights_Kleiman_DimTie_trdeg_polynomial_a210957d600c
