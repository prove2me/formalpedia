-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_DimTie_ringKrullDim_eq_62996ccb0278
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_DimTie_ringKrullDim_eq_62996ccb0278
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:59:34.014203+00:00
-- url     : https://prove2.me/theorems/d4a4be56-5422-4a4f-8162-7e6130b159b3
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Dim Tie ring Krull Dim eq 62996ccb0278: P2 M Ground Theory Heights  Heights Kleiman Dim Tie ring Krull Dim eq 62996ccb0278
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Dim Tie ring Krull Dim eq 62996ccb0278 construction uses the P2 M Ground Theory Heights  Heights Kleiman Dim Tie ring Krull Dim eq 62996ccb0278 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PDimTie.lean#L146-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PDimTie.lean#L146-L168

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_DimTie_ringKrullDim_eq_62996ccb0278 (y : Fin (N + 1) → Ω) (hy : y ≠ 0) :
    ringKrullDim (Poly k N ⧸ primeOf (S := k) y) =
      (((trdeg k (funField (k := k) y)).toENat + 1 : ℕ∞) : WithBot ℕ∞) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«DimTie».«ringKrullDim_eq» := P2M_GroundTheory_Heights__Heights_Kleiman_DimTie_ringKrullDim_eq_62996ccb0278
