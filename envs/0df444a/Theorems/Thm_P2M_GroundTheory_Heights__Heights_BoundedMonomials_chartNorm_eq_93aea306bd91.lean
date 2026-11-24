-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_BoundedMonomials_chartNorm_eq_93aea306bd91
-- name    : P2M_GroundTheory_Heights__Heights_BoundedMonomials_chartNorm_eq_93aea306bd91
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:50:16.014194+00:00
-- url     : https://prove2.me/theorems/f0cfaf3d-7d3f-4aa2-a53f-43358db1e235
-- title:
--   P2 M Ground Theory Heights  Heights Bounded Monomials chart Norm eq 93aea306bd91: P2 M Ground Theory Heights  Heights Bounded Monomials chart Norm eq 93aea306bd91
-- statement:
--   The P2 M Ground Theory Heights  Heights Bounded Monomials chart Norm eq 93aea306bd91 construction uses the P2 M Ground Theory Heights  Heights Bounded Monomials chart Norm eq 93aea306bd91 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZero.lean#L73-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZero.lean#L73-L100

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

theorem P2M_GroundTheory_Heights__Heights_BoundedMonomials_chartNorm_eq_93aea306bd91 {P : ArithVariety n} {A : HermLine n} (s : IntegralSection P A.deg) {z : Cone n ℂ}
    (hz : z ∈ P.points ℂ) {c c' : (k : ι) → Fin (n k + 1)} {d d' : ι → ℕ} {e e' : MvPolynomial (Coord n) ℤ}
    (he : IsChartForm P A.deg s.num s.den c d e) (he' : IsChartForm P A.deg s.num s.den c' d' e')
    (hc : ∀ k, z k (c k) ≠ 0) (hc' : ∀ k, z k (c' k) ≠ 0) :
    chartNorm A c d e z = chartNorm A c' d' e' z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«BoundedMonomials».«chartNorm_eq» := P2M_GroundTheory_Heights__Heights_BoundedMonomials_chartNorm_eq_93aea306bd91
