-- Prove2me | Theorems.Thm_ShiOptRates_CostModel_totalCost_const
-- name    : ShiOptRates.CostModel.totalCost_const
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-08T22:26:21.902989+00:00
-- url     : https://prove2.me/theorems/e833841c-65e8-4de5-b289-82e58bf79b60
-- title:
--   Total oracle cost of a constant accuracy schedule is $K$ times the unit price
-- statement:
--   A *cost model* $C$ is an oracle's price list: a function $\delta \mapsto C(\delta)$ giving the number of queries needed to answer to accuracy $\delta$, required to be nonnegative at positive accuracies. Given an accuracy schedule $\delta : \mathbb{N} \to \mathbb{R}$ and a horizon $K \in \mathbb{N}$, the total cost of running the schedule is
--
--   $$
--   \mathrm{Total}_C(\delta, K) \;=\; \sum_{k < K} C(\delta(k)).
--   $$
--
--   The theorem records the value of this sum for a constant schedule. For any cost model $C$, any accuracy $d \in \mathbb{R}$ and any $K \in \mathbb{N}$,
--
--   $$
--   \mathrm{Total}_C(k \mapsto d,\; K) \;=\; K \cdot C(d).
--   $$
--
--   Here $d$ is the accuracy requested at every iteration and $C(d)$ the unit price at that accuracy; no positivity or monotonicity of $C$ is needed.
--
--   Though elementary, this identity is the bridge every rate theorem in the library crosses when it converts an iteration count into a query count: the rate theorems produce a horizon $K$, the cost model supplies a unit price, and this lemma multiplies them. Specializing $C$ to classical minibatch averaging or to quantum multivariate mean estimation, and reading off the resulting constants, is exactly how one rate theorem yields the classical, inexact and quantum bills.
-- source:
--   lean-optrates, https://github.com/shiy1022/lean-optrates/blob/4c0b84980914ea7f9007510d92bcd60e91ad8448/Optrates/Cost.lean#L105-L108 (commit 4c0b84980914...) | Formalized in lean-optrates by Yueheng Shi. Original file licensed under the Apache License 2.0; the platform copy was produced by declaration-graph skeleton subtraction and the root namespace `OptRates` was renamed to `ShiOptRates`. No statement or proof was otherwise altered.

/-
Derived from lean-optrates -- https://github.com/shiy1022/lean-optrates
  commit 4c0b84980914ea7f9007510d92bcd60e91ad8448
  file   Optrates/Cost.lean
Original work Copyright (c) 2026 Yueheng Shi, released under the Apache License,
Version 2.0.  The original copyright and author notices are retained below.

MODIFICATIONS made for publication on Prove2me: declarations not reachable from
the published targets were removed by declaration-graph skeleton subtraction;
project imports were rewritten to platform `Definitions.Def_*` / `Theorems.Thm_*`
modules; the root namespace `OptRates` was renamed to `ShiOptRates`; the proof is replaced by `sorry`; 
no statement or proof was otherwise altered.

Built against Mathlib (Apache-2.0) at revision 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Definitions.Def_ShiOptrates_Cost
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yueheng Shi
-/

/-!
# L0 — Cost accounting

The piece of the library with no analogue in Mathlib or in the existing Lean
optimization formalizations: an oracle's *price list*.

A `CostModel` is a map from requested accuracy to number of queries.  A classical
minibatch mean estimator and a quantum multivariate mean estimator are two terms of this
one type, and — see `minibatch_eq_powerCost` and `quantumMean_eq_powerCost` — two members
of the same one-parameter family `PowerCost a p : cost δ = a / δ ^ p`, differing only in
the exponent `p` (`2` classical, `1` quantum).  Every rate separation proved in this
library is downstream of that single numeral.

## Main definitions

* `CostModel` — accuracy `↦` queries, nonnegative on positive accuracies.
* `CostModel.powerCost a p`, `CostModel.exact`, `CostModel.minibatch`,
  `CostModel.quantumMean` — the instances.
* `CostModel.totalCost C δ K` — `∑_{k<K} cost (δ k)`, the price of an accuracy schedule.

## Main results

* `totalCost_const` — constant schedule: `K * cost δ`.
* `totalCost_geometric` — geometric schedule against a power-law cost, in closed form.
* `totalCost_powerCost_const` — the form the rate theorems consume.
-/

section
open ShiOptRates

open Finset

section
open ShiOptRates
open ShiOptRates.CostModel

theorem ShiOptRates.CostModel.totalCost_const (C : CostModel) (d : ℝ) (K : ℕ) :
    C.totalCost (fun _ => d) K = K * C.cost d := by sorry
