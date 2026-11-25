-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_DimTie_isAlgebraic_range_b1cc57e8997d
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_DimTie_isAlgebraic_range_b1cc57e8997d
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T07:58:28.99705+00:00
-- url     : https://prove2.me/theorems/1c66813f-b6d5-5b9b-9a00-8fe649e4b6d2
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Dim Tie is Algebraic range b1cc57e8997d: P2 M Ground Theory Heights  Heights Kleiman Dim Tie is Algebraic range b1cc57e8997d
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Dim Tie is Algebraic range b1cc57e8997d construction uses the P2 M Ground Theory Heights  Heights Kleiman Dim Tie is Algebraic range b1cc57e8997d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PDimTie.lean#L87-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PDimTie.lean#L87-L128

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_DimTie_isAlgebraic_range_b1cc57e8997d :
    Algebra.IsAlgebraic (dehom (k := k) y hi₀).range (Polynomial (ratioRing (k := k) y)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«DimTie».«isAlgebraic_range» := P2M_GroundTheory_Heights__Heights_Kleiman_DimTie_isAlgebraic_range_b1cc57e8997d
