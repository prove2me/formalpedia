-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_BoundedMonomials_evalCone_chartMonomial_ne_zero_cbad317c02fd
-- name    : P2M_GroundTheory_Heights__Heights_BoundedMonomials_evalCone_chartMonomial_ne_zero_cbad317c02fd
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:49:42.950832+00:00
-- url     : https://prove2.me/theorems/d6754e74-d759-4c9a-9124-e06599e22302
-- title:
--   P2 M Ground Theory Heights  Heights Bounded Monomials eval Cone chart Monomial ne zero cbad317c02fd: P2 M Ground Theory Heights  Heights Bounded Monomials eval Cone chart Monomial ne zero cbad317c02fd
-- statement:
--   The P2 M Ground Theory Heights  Heights Bounded Monomials eval Cone chart Monomial ne zero cbad317c02fd construction uses the P2 M Ground Theory Heights  Heights Bounded Monomials eval Cone chart Monomial ne zero cbad317c02fd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZero.lean#L68-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZero.lean#L68-L71

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZero
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
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
open GroundTheory.Heights₂.Heights.BoundedMonomials
omit [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_BoundedMonomials_evalCone_chartMonomial_ne_zero_cbad317c02fd {z : Cone n ℂ} {c : (k : ι) → Fin (n k + 1)} (d : ι → ℕ)
    (hc : ∀ k, z k (c k) ≠ 0) : evalCone z (chartMonomial c d) ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«BoundedMonomials».«evalCone_chartMonomial_ne_zero» := P2M_GroundTheory_Heights__Heights_BoundedMonomials_evalCone_chartMonomial_ne_zero_cbad317c02fd
