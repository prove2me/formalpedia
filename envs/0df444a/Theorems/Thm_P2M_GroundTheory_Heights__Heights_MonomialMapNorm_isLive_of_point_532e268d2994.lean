-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MonomialMapNorm_isLive_of_point_532e268d2994
-- name    : P2M_GroundTheory_Heights__Heights_MonomialMapNorm_isLive_of_point_532e268d2994
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:50:19.876428+00:00
-- url     : https://prove2.me/theorems/662f1206-48c5-487f-bf32-71068beb3bbf
-- title:
--   P2 M Ground Theory Heights  Heights Monomial Map Norm is Live of point 532e268d2994: P2 M Ground Theory Heights  Heights Monomial Map Norm is Live of point 532e268d2994
-- statement:
--   The P2 M Ground Theory Heights  Heights Monomial Map Norm is Live of point 532e268d2994 construction uses the P2 M Ground Theory Heights  Heights Monomial Map Norm is Live of point 532e268d2994 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroBis.lean#L36-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroBis.lean#L36-L38

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZeroBis
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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.MonomialMapNorm
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable (P : ArithVariety n)
omit [Fintype ι]

theorem P2M_GroundTheory_Heights__Heights_MonomialMapNorm_isLive_of_point_532e268d2994 {z : Cone n ℂ} (hz : z ∈ P.points ℂ) {c : (k : ι) → Fin (n k + 1)}
    (hcz : ∀ k, z k (c k) ≠ 0) : P.IsLive c := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MonomialMapNorm».«isLive_of_point» := P2M_GroundTheory_Heights__Heights_MonomialMapNorm_isLive_of_point_532e268d2994
