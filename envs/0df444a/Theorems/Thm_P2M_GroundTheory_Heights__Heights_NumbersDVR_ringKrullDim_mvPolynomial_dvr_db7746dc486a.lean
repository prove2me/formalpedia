-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_ringKrullDim_mvPolynomial_dvr_db7746dc486a
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_ringKrullDim_mvPolynomial_dvr_db7746dc486a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:41:14.75865+00:00
-- url     : https://prove2.me/theorems/16653f98-6789-44d2-b123-06bd67e6ba9f
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR ring Krull Dim mv Polynomial dvr db7746dc486a: P2 M Ground Theory Heights  Heights Numbers DVR ring Krull Dim mv Polynomial dvr db7746dc486a
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR ring Krull Dim mv Polynomial dvr db7746dc486a construction uses the P2 M Ground Theory Heights  Heights Numbers DVR ring Krull Dim mv Polynomial dvr db7746dc486a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PComponentDim.lean#L20-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PComponentDim.lean#L20-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsComponentDim
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CycDim
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAB
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_WithBotEqOfLeOfAddOneLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PComponentDim
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
universe u
variable {σ : Type*} [Finite σ]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_ringKrullDim_mvPolynomial_dvr_db7746dc486a (O : Type*) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] :
    ringKrullDim (MvPolynomial σ O) = ((Nat.card σ + 1 : ℕ) : WithBot ℕ∞) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«ringKrullDim_mvPolynomial_dvr» := P2M_GroundTheory_Heights__Heights_NumbersDVR_ringKrullDim_mvPolynomial_dvr_db7746dc486a
