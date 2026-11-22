-- Prove2me | Theorems.Thm_ShiOptRates_quantum_query_count
-- name    : ShiOptRates.quantum_query_count
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-08T22:51:03.058117+00:00
-- url     : https://prove2.me/theorems/f3e01bf7-be60-4e68-8384-891b39d33891
-- title:
--   Query count of a quantum mean-estimation oracle over $K$ iterations: $K \cdot \mathrm{scale}\,\sqrt{d}\,\sigma\sqrt{2}/\varepsilon \cdot \log(K/\eta)$
-- statement:
--   A *cost model* is an oracle's price list: a function $\delta \mapsto C(\delta)$ giving the number of queries needed to answer to accuracy $\delta$, required to be nonnegative at positive accuracies. Given an accuracy schedule $\delta : \mathbb{N} \to \mathbb{R}$ and a horizon $K$, the total bill is $\sum_{k<K} C(\delta_k)$.
--
--   The quantum multivariate mean estimator has price list
--
--   $$
--   C(\delta) \;=\; \mathrm{scale}\cdot\sqrt{d}\cdot\frac{\sigma}{\delta}\cdot\log\!\frac{1}{\eta},
--   $$
--
--   where $d$ is the ambient dimension, $\sigma$ the noise scale, $\mathrm{scale} \ge 0$ an estimator-dependent prefactor, and $\eta \in (0,1]$ the allowed failure probability of a single call. Note the dependence on $1/\delta$ is *linear*, where a classical sample average pays $\sigma^{2}/\delta^{2}$.
--
--   Fix $K > 0$ iterations, $\sigma \ge 0$, $\mathrm{scale} \ge 0$, and a total failure budget $\eta > 0$ split evenly across iterations, so that each call is run at failure probability $\eta/K$ (assumed to satisfy $\eta/K \le 1$). Running the constant accuracy schedule $\delta_k \equiv \varepsilon/\sqrt{2}$ demanded by the inexact gradient-descent rate costs
--
--   $$
--   \sum_{k<K} C_{\eta/K}\!\left(\frac{\varepsilon}{\sqrt{2}}\right)
--   \;=\;
--   K\cdot\left(\mathrm{scale}\cdot\sqrt{d}\cdot\sigma\cdot\frac{\sqrt{2}}{\varepsilon}\cdot\log\frac{K}{\eta}\right).
--   $$
--
--   Composed with the iteration budget $K \asymp 4L\Delta_0/\varepsilon^{2}$ of the inexact gradient-descent rate, the right-hand side becomes $\asymp 4\sqrt{2}\,\mathrm{scale}\cdot L\Delta_0\,\sigma\sqrt{d}\,\log(K/\eta)/\varepsilon^{3}$. This is the $\sqrt{d}\,\varepsilon^{-3}$ quantum rate for smooth nonconvex optimization, with the union-bound logarithm from the failure schedule carried explicitly rather than absorbed into an $\widetilde{O}$. The statement itself is a pure cost computation: it contains no optimization content, which is exactly what lets one rate theorem serve the classical and quantum instantiations alike.
--
--   **Formalization Note** The failure probability enters the price list as $\log(1/\eta)$; substituting $\eta/K$ and rewriting gives the $\log(K/\eta)$ that appears on the right-hand side. The dimension is a natural number coerced into the square root, and the hypothesis $\varepsilon > 0$ is not needed for the identity.
-- source:
--   lean-optrates, https://github.com/shiy1022/lean-optrates/blob/4c0b84980914ea7f9007510d92bcd60e91ad8448/Optrates/Calibration.lean#L96-L114 (commit 4c0b84980914...) | Formalized in lean-optrates by Yueheng Shi. Original file licensed under the Apache License 2.0; the platform copy was produced by declaration-graph skeleton subtraction and the root namespace `OptRates` was renamed to `ShiOptRates`. No statement or proof was otherwise altered.

/-
Derived from lean-optrates -- https://github.com/shiy1022/lean-optrates
  commit 4c0b84980914ea7f9007510d92bcd60e91ad8448
  file   Optrates/Calibration.lean
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
import Definitions.Def_ShiOptrates_FunctionClass
import Theorems.Thm_ShiOptRates_CostModel_totalCost_const
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yueheng Shi
-/

/-!
# §5 — Calibration theorems

The library's evidence: named rates, stated with explicit constants, each obtained by
instantiating the *same* L1/L2 theorems at a different oracle contract and cost model.

| theorem | layer | rate |
|---|---|---|
| `gd_exact_rate` | L1 | `K ≥ 2LΔ₀/ε²` gradient evaluations |
| `inexact_gd_rate` | L1 | `K ≥ 4LΔ₀/ε²` iterations at accuracy `ε/√2` |
| `minibatch_query_count` | L1 | `≍ 8 L Δ₀ σ² / ε⁴` samples |
| `quantum_query_count` | L1+L2 | `≍ 4√2 · L Δ₀ σ √dim log(K/η) / ε³` queries |

The classical `ε⁻⁴` and the quantum `ε⁻³` are produced by the same iteration bound
`K ≍ 4LΔ₀/ε²` multiplied by two different unit prices; nothing else differs.  See
`Optrates.Cost` for why those two prices are one formula at two exponents.

**Not formalized here** (L3+, per the plan's layering): SGD's `ε⁻⁴` *under an unbiased
stochastic oracle over an adaptive filtration*, SPIDER's `ε⁻³`, and Q-SPIDER's `ε⁻⁵ᐟ²`.
The `ε⁻⁴` below is the deterministic-surrogate version — a minibatch large enough to give
a *deterministic* accuracy guarantee — which is a strictly stronger oracle assumption than
SGD's and therefore not a reproduction of Ghadimi–Lan.  Stating this distinction rather
than eliding it is the point of the layering.
-/

section
open ShiOptRates

open Finset MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {f : E → ℝ} {g : E → E} {L : ℝ}

theorem ShiOptRates.quantum_query_count (dim : ℕ) (σ η scale ε : ℝ) (K : ℕ) (hK : 0 < K)
    (hσ : 0 ≤ σ) (hscale : 0 ≤ scale) (hη0 : 0 < η) (hηK : η / K ≤ 1) (_hε : 0 < ε) :
    (CostModel.quantumMean dim σ (η / K) scale hσ hscale (by positivity)
        hηK).totalCost (fun _ => ε / Real.sqrt 2) K
      = K * (scale * Real.sqrt dim * σ * Real.sqrt 2 / ε * Real.log (K / η)) := by sorry
