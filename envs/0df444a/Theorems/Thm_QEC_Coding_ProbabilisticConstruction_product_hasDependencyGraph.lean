-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_product_hasDependencyGraph
-- name    : QEC.Coding.ProbabilisticConstruction.product_hasDependencyGraph
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:18:42.817857+00:00
-- url     : https://prove2.me/theorems/f2f14ea5-7085-4e21-892c-2ff024d8e8be
-- title:
--   Probabilistic Construction: product has Dependency Graph
-- statement:
--   Independent coordinate laws derive joint nonneighbor independence of all local events.
--   The complement tuple contains every nonneighbor's coordinates simultaneously.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/LocalLemma.lean#L214-L247
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/LocalLemma.lean#L214-L247

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

theorem QEC.Coding.ProbabilisticConstruction.product_hasDependencyGraph (ν : ∀ v, Measure (X v))
    [∀ v, IsProbabilityMeasure (ν v)] (vars : I → Finset V)
    (bad : ∀ i, Set (∀ v : vars i, X v)) (hbad : ∀ i, MeasurableSet (bad i)) :
    HasDependencyGraph (Measure.pi ν) (localEvent vars bad) (supportGraph vars) := by sorry
