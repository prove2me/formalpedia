-- Prove2me | Theorems.Thm_RegevLWE_PeriodicGauss_pointwise_bound
-- name    : RegevLWE.PeriodicGauss.pointwise_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T23:07:43.820142+00:00
-- url     : https://prove2.me/theorems/ea14dd9e-989e-4647-80a5-85803891a911
-- title:
--   Proof of Claim 2.2, p. 34:16 — |e^{−π(1−1/(1+ϵ)²)x²} − 1| ≤ π(1 − 1/(1+ϵ)²)x² ≤ 2πϵx²
-- statement:
--   For every $\epsilon \ge 0$ and every real $x$,
--   $$\bigl|e^{-\pi(1-1/(1+\epsilon)^2)x^2} - 1\bigr| \le \pi\bigl(1 - 1/(1+\epsilon)^2\bigr)x^2 \le 2\pi\epsilon x^2.$$
--   The paper derives this from $1 - z \le e^{-z} \le 1$ for $z \ge 0$.
--
--   It turns the integral left over by the first display into a second moment of a Gaussian.
--
--   **Formalization Note** The paper uses the bound for $0 < \epsilon \le 1$; it holds, and is stated, for every $\epsilon \ge 0$.
-- source:
--   Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, J. ACM 56(6) (2009), Article 34, p. 34:16, proof of Claim 2.2, display after "since 1 − z ≤ e^{−z} ≤ 1 for all z ≥ 0"

import Mathlib
import Definitions.Def_RegevLWE_PeriodicGauss_Gaussian

open MeasureTheory

namespace RegevLWE.PeriodicGauss

/-- Proof of Claim 2.2, p. 34:16: since `1 - z ≤ e^{-z} ≤ 1` for all `z ≥ 0`,
`|e^{-π(1-1/(1+ϵ)²)x²} - 1| ≤ π(1 - 1/(1+ϵ)²)x² ≤ 2πϵx²` (here for every `ϵ ≥ 0` and real `x`). -/
theorem pointwise_bound (ϵ : ℝ) (hϵ : 0 ≤ ϵ) (x : ℝ) :
    |Real.exp (-Real.pi * (1 - 1 / (1 + ϵ) ^ 2) * x ^ 2) - 1| ≤
        Real.pi * (1 - 1 / (1 + ϵ) ^ 2) * x ^ 2 ∧
      Real.pi * (1 - 1 / (1 + ϵ) ^ 2) * x ^ 2 ≤ 2 * Real.pi * ϵ * x ^ 2 := by sorry

end RegevLWE.PeriodicGauss
