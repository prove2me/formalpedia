-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_localLemma_product_lower
-- name    : QEC.Coding.ProbabilisticConstruction.localLemma_product_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:09:15.692168+00:00
-- url     : https://prove2.me/theorems/1069df6a-fb06-4113-87aa-a491d08cf146
-- title:
--   Probabilistic Construction: local Lemma product lower
-- statement:
--   Avoidance has the asymmetric product lower bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/LocalLemma.lean#L167-L172
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/LocalLemma.lean#L167-L172

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_LocalLemma
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (B : I → Set Ω) (hB : ∀ i, MeasurableSet (B i))
variable (x : I → ℝ) (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
include hB
variable (G : SimpleGraph I) [DecidableRel G.Adj]
variable (hdep : HasDependencyGraph μ B G)
variable (hcrit : ∀ i, μ.real (B i) ≤ x i * ∏ j ∈ G.neighborFinset i, (1 - x j))
include hx0 hx1 hdep hcrit

theorem QEC.Coding.ProbabilisticConstruction.localLemma_product_lower (S : Finset I) :
    (∏ i ∈ S, (1 - x i)) ≤ μ.real (avoid B S) := by sorry
