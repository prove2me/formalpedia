-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MonomialMapNorm_form_div_mem_df5c07c6a0e3
-- name    : P2M_GroundTheory_Heights__Heights_MonomialMapNorm_form_div_mem_df5c07c6a0e3
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:51:50.061391+00:00
-- url     : https://prove2.me/theorems/14705d8e-05ff-5cf3-9efe-feb0a18dd39e
-- title:
--   P2 M Ground Theory Heights  Heights Monomial Map Norm form div mem df5c07c6a0e3: P2 M Ground Theory Heights  Heights Monomial Map Norm form div mem df5c07c6a0e3
-- statement:
--   The P2 M Ground Theory Heights  Heights Monomial Map Norm form div mem df5c07c6a0e3 construction uses the P2 M Ground Theory Heights  Heights Monomial Map Norm form div mem df5c07c6a0e3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroBis.lean#L53-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroBis.lean#L53-L63

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

theorem P2M_GroundTheory_Heights__Heights_MonomialMapNorm_form_div_mem_df5c07c6a0e3 {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c) {e : MvPolynomial (Coord n) ℤ}
    {δ : ι → ℕ} (he : IsWeightedHomogeneous (coordDeg n) e δ) :
    P.mkF e / P.chartPow c (fun k ↦ (δ k : ℤ)) ∈ P.chartRing c := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MonomialMapNorm».«form_div_mem» := P2M_GroundTheory_Heights__Heights_MonomialMapNorm_form_div_mem_df5c07c6a0e3
