-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MonomialMapNorm_evalCone_chartMonomial_ne_zero_74ae91588762
-- name    : P2M_GroundTheory_Heights__Heights_MonomialMapNorm_evalCone_chartMonomial_ne_zero_74ae91588762
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:29:08.510239+00:00
-- url     : https://prove2.me/theorems/a0b43cec-904d-4821-aae3-cad42598b291
-- title:
--   P2 M Ground Theory Heights  Heights Monomial Map Norm eval Cone chart Monomial ne zero 74ae91588762: P2 M Ground Theory Heights  Heights Monomial Map Norm eval Cone chart Monomial ne zero 74ae91588762
-- statement:
--   The P2 M Ground Theory Heights  Heights Monomial Map Norm eval Cone chart Monomial ne zero 74ae91588762 construction uses the P2 M Ground Theory Heights  Heights Monomial Map Norm eval Cone chart Monomial ne zero 74ae91588762 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroBis.lean#L27-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroBis.lean#L27-L30

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
omit [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_MonomialMapNorm_evalCone_chartMonomial_ne_zero_74ae91588762 {z : Cone n ℂ} {c : (k : ι) → Fin (n k + 1)}
    (hcz : ∀ k, z k (c k) ≠ 0) (d : ι → ℕ) : evalCone z (chartMonomial c d) ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MonomialMapNorm».«evalCone_chartMonomial_ne_zero» := P2M_GroundTheory_Heights__Heights_MonomialMapNorm_evalCone_chartMonomial_ne_zero_74ae91588762
