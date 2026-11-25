-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_ringKrullDim_le_of_isAlgebraic_adjoin_singleton_7a17107463fa
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_ringKrullDim_le_of_isAlgebraic_adjoin_singleton_7a17107463fa
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:12:49.091193+00:00
-- url     : https://prove2.me/theorems/af26244e-4a5d-4136-92e4-d3d54846ec89
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR ring Krull Dim le of is Algebraic adjoin singleton 7a17107463fa: P2 M Ground Theory Heights  Heights Numbers DVR ring Krull Dim le of is Algebraic adjoi
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR ring Krull Dim le of is Algebraic adjoin singleton 7a17107463fa construction uses the P2 M Ground Theory Heights  Heights Numbers DVR ring Krull Dim le of is Algebraic adjoin singleton 7a17107463fa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/RingKrullDimLeOfIsAlgebraicAdjoinSingleton.lean#L21-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/RingKrullDimLeOfIsAlgebraicAdjoinSingleton.lean#L21-L44

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ComapLiftFormConstChartPrimeExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_LiftFormNotMemBlowUpOf
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PComponentDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTopDimMinimal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDimStrictDrop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_AssemblyDimensionInequality
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_RingKrullDimLeOfIsAlgebraicAdjoinSingleton
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
universe u
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_ringKrullDim_le_of_isAlgebraic_adjoin_singleton_7a17107463fa {A B : Type u} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [CommRing B] [IsDomain B] [Algebra A B] [Algebra.FiniteType A B]
    (hinj : Function.Injective (algebraMap A B)) (y : B)
    [Algebra.IsAlgebraic (Algebra.adjoin A ({y} : Set B)) B] (N : ℕ)
    (hA : ringKrullDim A < (N : WithBot ℕ∞)) : ringKrullDim B ≤ (N : WithBot ℕ∞) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«ringKrullDim_le_of_isAlgebraic_adjoin_singleton» := P2M_GroundTheory_Heights__Heights_NumbersDVR_ringKrullDim_le_of_isAlgebraic_adjoin_singleton_7a17107463fa
