-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_product_localLemma
-- name    : QEC.Coding.ProbabilisticConstruction.product_localLemma
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:41:21.3442+00:00
-- url     : https://prove2.me/theorems/0fb1d7e7-e87f-411a-8cf2-1f5163b609e8
-- title:
--   Probabilistic Construction: product local Lemma
-- statement:
--   Product-variable asymmetric LLL: independence is proved from the local supports.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/LocalLemma.lean#L250-L267
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/LocalLemma.lean#L250-L267

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
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]

theorem QEC.Coding.ProbabilisticConstruction.product_localLemma (ν : ∀ v, Measure (X v))
    [∀ v, IsProbabilityMeasure (ν v)] (vars : I → Finset V)
    (bad : ∀ i, Set (∀ v : vars i, X v)) (hbad : ∀ i, MeasurableSet (bad i))
    (x : I → ℝ) (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (hcrit : ∀ i, (Measure.pi ν).real (localEvent vars bad i) ≤
      x i * ∏ j ∈ (supportGraph vars).neighborFinset i, (1 - x j)) :
    (∀ S, (∏ i ∈ S, (1 - x i)) ≤ (Measure.pi ν).real (avoid (localEvent vars bad) S)) ∧
    (∀ S, 0 < (Measure.pi ν).real (avoid (localEvent vars bad) S)) ∧
    (∀ S i, i ∉ S → (Measure.pi ν).real (localEvent vars bad i ∩
      avoid (localEvent vars bad) S) ≤ x i * (Measure.pi ν).real
        (avoid (localEvent vars bad) S)) ∧
    (∃ ω, ∀ i, ω ∉ localEvent vars bad i) := by sorry
