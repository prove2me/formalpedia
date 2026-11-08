-- Prove2me | Theorems.Thm_PercCubeCycles_theorem_4
-- name    : PercCubeCycles.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:32:28.941639+00:00
-- url     : https://prove2.me/theorems/0c3931e8-f6a6-4c14-8187-eb6e3d45b44e
-- title:
--   Theorem 4 — Chernoff: $\Pr[|X-\mathbb EX|\ge t]\le2\exp(-t^2/(3\mathbb E[X]))$
-- statement:
--   For a binomial random variable $X$ and any $t\in[0,\mathbb E[X]]$,
--   $$\Pr[|X-\mathbb EX|\ge t]\le2\exp\left(-\frac{t^2}{3\mathbb E[X]}\right).$$
--   This is the Chernoff bound the paper uses for binomial counts.
--
--   Differences from the source:
--   - encoding: $X$ binomial, $\mathbb E[X]$ → `ProbabilityTheory.binomial n p`, with $\mathbb E[X]=np$; reason: the mean is written out
--   - encoding: the bound at $\mathbb E[X]=0$ → $t=0$ and the bound is $2$, since $0/0=0$ in Lean; reason: the printed bound is undefined there, and the statement is trivially true
-- source:
--   Anastos, Linear-length cycles in the supercritical percolated hypercube, STOC 2027 submission (sha256 14e6f0eeea86205c661b9ec5b7259d5e903f4bcfacef3946a425ea6e60e837ae), Theorem 4, p.7

import Mathlib

set_option autoImplicit false

namespace PercCubeCycles

/-- Theorem 4, p.7 (Chernoff bound), Anastos, *Linear-length cycles in the supercritical percolated hypercube*, STOC 2027 submission (sha256 14e6f0ee…). For a binomial random variable `X` and any
`t ∈ [0, E[X]]`, `Pr[|X − E X| ≥ t] ≤ 2 exp(−t² / (3 E[X]))`.

**Formalization Note.** `X ∼ Bin(n, p)` is `ProbabilityTheory.binomial n p`, with `E[X] = np`. At `np = 0`
the range forces `t = 0`, and the bound is `2` (`0 / 0 = 0` in Lean), which is true. -/
theorem theorem_4 (n : ℕ) (p : unitInterval) (t : ℝ) (ht₀ : 0 ≤ t) (ht : t ≤ n * (p : ℝ)) :
    ProbabilityTheory.binomial n p {x : ℕ | t ≤ |(x : ℝ) - n * (p : ℝ)|}
      ≤ ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (3 * (n * (p : ℝ))))) := by sorry

end PercCubeCycles
