-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GoodChartDim_proof_c39224e52d11
-- name    : P2M_GroundTheory_Heights__Heights_GoodChartDim_proof_c39224e52d11
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T17:09:27.977721+00:00
-- url     : https://prove2.me/theorems/ebdc60f6-af26-5268-83b4-d3e7cafa7799
-- title:
--   P2 M Ground Theory Heights  Heights Good Chart Dim proof c39224e52d11: P2 M Ground Theory Heights  Heights Good Chart Dim proof c39224e52d11
-- statement:
--   The P2 M Ground Theory Heights  Heights Good Chart Dim proof c39224e52d11 construction uses the P2 M Ground Theory Heights  Heights Good Chart Dim proof c39224e52d11 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PGoodChartDim.lean#L114-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PGoodChartDim.lean#L114-L172

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
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartDehomog_proof_43d0929de030
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartHomogenise_proof_a08065262b6f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartLocDomain_proof_34872f657b6a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GoodChartZeroSet_proof_337a19539709
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SegreChartDim_proof_4e503d72b794
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SegreChartZeroSet_proof_17ca30ede7f1

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
open GoodChartDim

theorem P2M_GroundTheory_Heights__Heights_GoodChartDim_proof_c39224e52d11 (h₁ : ConeVanishingHomog.Statement) (h₂ : ConeSliceIdeal.Statement)
    (h₃ : ChartDehomogPrime.Statement) : GoodChartDim.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GoodChartDim».«proof» := P2M_GroundTheory_Heights__Heights_GoodChartDim_proof_c39224e52d11
