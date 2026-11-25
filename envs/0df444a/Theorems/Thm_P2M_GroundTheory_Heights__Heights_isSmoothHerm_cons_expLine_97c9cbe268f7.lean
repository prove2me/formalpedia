-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_isSmoothHerm_cons_expLine_97c9cbe268f7
-- name    : P2M_GroundTheory_Heights__Heights_isSmoothHerm_cons_expLine_97c9cbe268f7
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:48:01.44749+00:00
-- url     : https://prove2.me/theorems/3ccca5f9-74bc-435e-bd97-7fb3a229f7fb
-- title:
--   P2 M Ground Theory Heights  Heights is Smooth Herm cons exp Line 97c9cbe268f7: P2 M Ground Theory Heights  Heights is Smooth Herm cons exp Line 97c9cbe268f7
-- statement:
--   The P2 M Ground Theory Heights  Heights is Smooth Herm cons exp Line 97c9cbe268f7 construction uses the P2 M Ground Theory Heights  Heights is Smooth Herm cons exp Line 97c9cbe268f7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSegreChart.lean#L27-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSegreChart.lean#L27-L34

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegreChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegreChartDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegreChartIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegreChart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_isOpen_blockNonzero

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
open Filter Topology
open scoped ContDiff
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar ptsIntegral pot segre isOpen_blockNonzero)

theorem P2M_GroundTheory_Heights__Heights_isSmoothHerm_cons_expLine_97c9cbe268f7 {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {n : ℕ}
    (v : ((Σ k, ι k) → ℂ) → ℝ) (hv : IsDegZeroSmooth v) (L : Fin n → HermLine ι)
    (hL : ∀ j, IsSmoothHerm (L j)) :
    ∀ j, IsSmoothHerm ((Fin.cons (expLine v hv) L : Fin (n + 1) → HermLine ι) j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«isSmoothHerm_cons_expLine» := P2M_GroundTheory_Heights__Heights_isSmoothHerm_cons_expLine_97c9cbe268f7
