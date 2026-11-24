-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MonomialMapNorm_mkF_X_ne_zero_610853a0b298
-- name    : P2M_GroundTheory_Heights__Heights_MonomialMapNorm_mkF_X_ne_zero_610853a0b298
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:58:49.603086+00:00
-- url     : https://prove2.me/theorems/f5800e7a-430e-4501-abfc-ffdb765a79e7
-- title:
--   P2 M Ground Theory Heights  Heights Monomial Map Norm mk F X ne zero 610853a0b298: P2 M Ground Theory Heights  Heights Monomial Map Norm mk F X ne zero 610853a0b298
-- statement:
--   The P2 M Ground Theory Heights  Heights Monomial Map Norm mk F X ne zero 610853a0b298 construction uses the P2 M Ground Theory Heights  Heights Monomial Map Norm mk F X ne zero 610853a0b298 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroBis.lean#L41-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroBis.lean#L41-L42

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

theorem P2M_GroundTheory_Heights__Heights_MonomialMapNorm_mkF_X_ne_zero_610853a0b298 {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c) (k : ι) :
    P.mkF (X ⟨k, c k⟩) ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MonomialMapNorm».«mkF_X_ne_zero» := P2M_GroundTheory_Heights__Heights_MonomialMapNorm_mkF_X_ne_zero_610853a0b298
