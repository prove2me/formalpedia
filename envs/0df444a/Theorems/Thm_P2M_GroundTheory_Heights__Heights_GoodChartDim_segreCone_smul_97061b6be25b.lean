-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GoodChartDim_segreCone_smul_97061b6be25b
-- name    : P2M_GroundTheory_Heights__Heights_GoodChartDim_segreCone_smul_97061b6be25b
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T16:30:13.267537+00:00
-- url     : https://prove2.me/theorems/ab1f7a28-72a7-518e-adb8-ff67d7dcce0b
-- title:
--   P2 M Ground Theory Heights  Heights Good Chart Dim segre Cone smul 97061b6be25b: P2 M Ground Theory Heights  Heights Good Chart Dim segre Cone smul 97061b6be25b
-- statement:
--   The P2 M Ground Theory Heights  Heights Good Chart Dim segre Cone smul 97061b6be25b construction uses the P2 M Ground Theory Heights  Heights Good Chart Dim segre Cone smul 97061b6be25b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PGoodChartDim.lean#L27-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PGoodChartDim.lean#L27-L32

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

theorem P2M_GroundTheory_Heights__Heights_GoodChartDim_segreCone_smul_97061b6be25b {P : Ideal (MRing ι)} {d : ℕ} (hP : IsArithVar P d) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) :
    ∀ c ∈ segreCone P σ, ∀ a : ℂ, a ≠ 0 → a • c ∈ segreCone P σ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GoodChartDim».«segreCone_smul» := P2M_GroundTheory_Heights__Heights_GoodChartDim_segreCone_smul_97061b6be25b
