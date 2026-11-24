-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MonomialMap_chart_value_eq_f30369e8f416
-- name    : P2M_GroundTheory_Heights__Heights_MonomialMap_chart_value_eq_f30369e8f416
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:28:51.16011+00:00
-- url     : https://prove2.me/theorems/ce2272c1-089c-4c4b-b075-5fba27e8c286
-- title:
--   P2 M Ground Theory Heights  Heights Monomial Map chart value eq f30369e8f416: P2 M Ground Theory Heights  Heights Monomial Map chart value eq f30369e8f416
-- statement:
--   The P2 M Ground Theory Heights  Heights Monomial Map chart value eq f30369e8f416 construction uses the P2 M Ground Theory Heights  Heights Monomial Map chart value eq f30369e8f416 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroAlt.lean#L39-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroAlt.lean#L39-L53

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZeroAlt
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
open GroundTheory.Heights₂.Heights.MonomialMap
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

theorem P2M_GroundTheory_Heights__Heights_MonomialMap_chart_value_eq_f30369e8f416 {P : ArithVariety n} {num den e e' : MvPolynomial (Coord n) ℤ}
    {c : (k : ι) → Fin (n k + 1)} {d d' : ι → ℕ} (hden : den ∉ P.ideal)
    (h₁ : den * e - num * chartMonomial c d ∈ P.ideal)
    (h₂ : den * e' - num * chartMonomial c d' ∈ P.ideal) {z : Cone n ℂ} (hz : z ∈ P.points ℂ) :
    evalCone z e * evalCone z (chartMonomial c d') =
      evalCone z e' * evalCone z (chartMonomial c d) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MonomialMap».«chart_value_eq» := P2M_GroundTheory_Heights__Heights_MonomialMap_chart_value_eq_f30369e8f416
