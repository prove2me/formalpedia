-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsIntegralZeroLowerNEAux_segre_ne_zero_dd2ca74dbc07
-- name    : P2M_GroundTheory_Heights__Heights_PtsIntegralZeroLowerNEAux_segre_ne_zero_dd2ca74dbc07
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:21:14.379888+00:00
-- url     : https://prove2.me/theorems/9fe3b69e-33e5-533c-a9cf-01fa5d19be2d
-- title:
--   P2 M Ground Theory Heights  Heights Pts Integral Zero Lower NEAux segre ne zero dd2ca74dbc07: P2 M Ground Theory Heights  Heights Pts Integral Zero Lower NEAux segre ne zero dd2ca74dbc07
-- statement:
--   The P2 M Ground Theory Heights  Heights Pts Integral Zero Lower NEAux segre ne zero dd2ca74dbc07 construction uses the P2 M Ground Theory Heights  Heights Pts Integral Zero Lower NEAux segre ne zero dd2ca74dbc07 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PPtsIntegralZeroLowerNE.lean#L49-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PPtsIntegralZeroLowerNE.lean#L49-L54

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeightNE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PPtsIntegralZeroLowerNE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial MeasureTheory
noncomputable section
open GroundTheory.Heights₂.Heights.PtsIntegralZeroLowerNEAux
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_PtsIntegralZeroLowerNEAux_segre_ne_zero_dd2ca74dbc07 {W : Ideal (MRing ι)} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts W) : segre z ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PtsIntegralZeroLowerNEAux».«segre_ne_zero» := P2M_GroundTheory_Heights__Heights_PtsIntegralZeroLowerNEAux_segre_ne_zero_dd2ca74dbc07
