-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_pot_cons_expLine_9bc1a22b6dbc
-- name    : P2M_GroundTheory_Heights__Heights_pot_cons_expLine_9bc1a22b6dbc
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:49:51.842853+00:00
-- url     : https://prove2.me/theorems/cc827332-3057-4d95-837d-8534b09f2935
-- title:
--   P2 M Ground Theory Heights  Heights pot cons exp Line 9bc1a22b6dbc: P2 M Ground Theory Heights  Heights pot cons exp Line 9bc1a22b6dbc
-- statement:
--   The P2 M Ground Theory Heights  Heights pot cons exp Line 9bc1a22b6dbc construction uses the P2 M Ground Theory Heights  Heights pot cons exp Line 9bc1a22b6dbc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSegreChart.lean#L19-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSegreChart.lean#L19-L25

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

theorem P2M_GroundTheory_Heights__Heights_pot_cons_expLine_9bc1a22b6dbc {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {n : ℕ}
    (v : ((Σ k, ι k) → ℂ) → ℝ) (hv : IsDegZeroSmooth v) (L : Fin n → HermLine ι) :
    pot (Fin.cons (expLine v hv) L : Fin (n + 1) → HermLine ι) = Fin.cons v (pot L) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«pot_cons_expLine» := P2M_GroundTheory_Heights__Heights_pot_cons_expLine_9bc1a22b6dbc
