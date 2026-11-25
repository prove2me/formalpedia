-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GoodChartDim_segreChartSet_eq_6edfe04a2f43
-- name    : P2M_GroundTheory_Heights__Heights_GoodChartDim_segreChartSet_eq_6edfe04a2f43
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T16:26:03.509594+00:00
-- url     : https://prove2.me/theorems/725df441-a7cc-4aeb-9698-340978ecbb59
-- title:
--   P2 M Ground Theory Heights  Heights Good Chart Dim segre Chart Set eq 6edfe04a2f43: P2 M Ground Theory Heights  Heights Good Chart Dim segre Chart Set eq 6edfe04a2f43
-- statement:
--   The P2 M Ground Theory Heights  Heights Good Chart Dim segre Chart Set eq 6edfe04a2f43 construction uses the P2 M Ground Theory Heights  Heights Good Chart Dim segre Chart Set eq 6edfe04a2f43 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PGoodChartDim.lean#L60-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PGoodChartDim.lean#L60-L68

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StGoodChartDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StConeVanishingHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StConeSliceIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StChartDehomogPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegreChartDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PGoodChartZeroSet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartHomogenise
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartDehomog
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PGoodChartDim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar mcPts segre)
open GroundTheory.Heights₂.Heights.GoodChartDim
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_GoodChartDim_segreChartSet_eq_6edfe04a2f43 (P : Ideal (MRing ι)) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (a : Fin m) :
    segreChartSet P σ (σ a) = {x | x ∈ segreCone P σ ∧ eval x (linForm (Pi.single a (1 : ℂ))) = 1} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GoodChartDim».«segreChartSet_eq» := P2M_GroundTheory_Heights__Heights_GoodChartDim_segreChartSet_eq_6edfe04a2f43
