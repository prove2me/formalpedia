-- Prove2me | Theorems.Thm_ThinShellSampling_corollary_1_3
-- name    : ThinShellSampling.corollary_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:47:18.112892+00:00
-- url     : https://prove2.me/theorems/fce1bed5-ab95-4662-8066-c26950650be8
-- title:
--   Corollary 1.3 — hypercontractivity of the proximal sampler
-- statement:
--   Let $\pi^X$ be a probability measure on $\mathbb R^n$ satisfying (LSI) with constant $C>0$, let $h>0$, and let $\pi^X_N$ be the law of the $N$-th iterate of the Proximal sampler with step size $h$, initial law $\pi^X_0$ and target $\pi^X$. There is a universal constant $C_0$ such that:
--
--   1. for $1<p\le q$ and every $N\ge C_0\,\{1\vee h^{-1}C\}\log_2\frac{q-1}{p-1}$,
--   $$\mathsf R_q(\pi^X_N\,\|\,\pi^X)\le\mathsf R_p(\pi^X_0\,\|\,\pi^X);$$
--   2. for $\varepsilon>0$, $q\ge q_0>1$ with $\mathsf R_{2\wedge q_0}(\pi^X_0\,\|\,\pi^X)<\infty$, and every
--   $$N\ge C_0\,\{1\vee h^{-1}C\}\log\frac{q\,\big(\varepsilon\vee\mathsf R_{2\wedge q_0}(\pi^X_0\,\|\,\pi^X)\big)}{(2\wedge q_0-1)\,\varepsilon},$$
--   one has $\mathsf R_q(\pi^X_N\,\|\,\pi^X)\le\varepsilon$.
--
--   The proximal sampler thus preserves the Rényi order of a warm start (first clause) and converges in every Rényi order at a rate logarithmic in $q$ (second clause); this is the mixing input to Proposition 6.5.
--
--   Differences from the source:
--
--   - generalization: C_LSI(π^X) → every C > 0 with LSI C π^X; reason: the least constant is attained, so C = C_LSI(π^X) gives the printed statement
--   - reading: "after N ≲ X iterations" → for every N ≥ C₀·X with a universal constant C₀; reason: the guarantee is monotone in N by data processing, so every larger N also works; the paper's ≲ is a universal constant
--   - encoding: second clause for an arbitrary initial law → hypothesis R_{2∧q₀}(π^X_0 ‖ π^X) < ∞; reason: when it is infinite the printed iteration count is infinite and the clause is empty
-- source:
--   Kook, Vempala, Thin-Shell Stability and Heat-Adjoint Hypercontractivity: Logconcave Sampling with Sesteric Complexity from a Cold Start, STOC 2027 submission (manuscript sha256 25a041a9…), Corollary 1.3, p.3 (PDF p.5); proof pp.23–24 (PDF pp.25–26)

import Mathlib
import Definitions.Def_ThinShellSampling_renyi
import Definitions.Def_ThinShellSampling_LSI
import Definitions.Def_ThinShellSampling_proxIter

set_option autoImplicit false

namespace ThinShellSampling

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- **Corollary 1.3 (Hypercontractivity of proximal sampler).**

Y. Kook, S. S. Vempala, *Thin-Shell Stability and Heat-Adjoint Hypercontractivity: Logconcave
Sampling with Sesteric Complexity from a Cold Start*, STOC 2027 submission (manuscript sha256
25a041a9…), Corollary 1.3, p.3 (PDF p.5): "Let `π^X_k` be the law of the `k`-th iterate returned by the
Proximal sampler with step size `h > 0`, initial `π^X_0`, and target `π^X`. Given `1 < p ≤ q`, we have
`R_q(π^X_N ‖ π^X) ≤ R_p(π^X_0 ‖ π^X)` after `N ≲ {1 ∨ h⁻¹C_LSI(π^X)} log₂ ((q−1)/(p−1))` iterations.
Moreover, given `ε > 0` and `q ≥ q₀ > 1`, we have `R_q(π^X_N ‖ π^X) ≤ ε` after
`N ≲ (1 ∨ h⁻¹C_LSI(π^X)) log [q (ε ∨ R_{2∧q₀}(π^X_0 ‖ π^X)) / ((2 ∧ q₀ − 1) ε)]` iterations."

**Formalization Note.** "After `N ≲ X` iterations" is read as: there is a universal constant `C₀`
such that the guarantee holds for **every** `N ≥ C₀·X`. `C_LSI(π^X)` is replaced by any `C > 0` with
`LSI C π^X`. In the second clause the bound is meaningful only when `R_{2∧q₀}(π^X_0 ‖ π^X) < ∞` (for
`R = ∞` the printed iteration count is infinite), so finiteness is a hypothesis. -/
theorem corollary_1_3 :
    ∃ C₀ : ℝ, 0 < C₀ ∧
    ∀ (n : ℕ) (π : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
      (π₀ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure π₀] (h C : ℝ),
      0 < h → 0 < C → LSI C π →
      (∀ p q : ℝ, 1 < p → p ≤ q → ∀ N : ℕ,
          C₀ * max 1 (C / h) * Real.logb 2 ((q - 1) / (p - 1)) ≤ N →
          renyi q (proxIter n (π : Measure (EuclideanSpace ℝ (Fin n))) h N π₀)
              (π : Measure (EuclideanSpace ℝ (Fin n))) ≤
            renyi p π₀ (π : Measure (EuclideanSpace ℝ (Fin n)))) ∧
      (∀ ε q q₀ : ℝ, 0 < ε → 1 < q₀ → q₀ ≤ q →
          renyi (min 2 q₀) π₀ (π : Measure (EuclideanSpace ℝ (Fin n))) ≠ ⊤ → ∀ N : ℕ,
          C₀ * max 1 (C / h) *
              Real.log (q * max ε (renyi (min 2 q₀) π₀
                  (π : Measure (EuclideanSpace ℝ (Fin n)))).toReal / ((min 2 q₀ - 1) * ε)) ≤ N →
          renyi q (proxIter n (π : Measure (EuclideanSpace ℝ (Fin n))) h N π₀)
              (π : Measure (EuclideanSpace ℝ (Fin n))) ≤ ENNReal.ofReal ε) := by sorry

end ThinShellSampling
