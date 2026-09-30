-- Prove2me | Theorems.Thm_TierneyMH_Peskun_asymptotic_variance_exists
-- name    : TierneyMH.Peskun.asymptotic_variance_exists
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T12:42:39.138674+00:00
-- url     : https://prove2.me/theorems/0aca3722-347d-4d0e-9deb-20c67d4d4d86
-- title:
--   The asymptotic variance $v(f,H)$ exists in $[0,\infty]$
-- statement:
--   Let $\pi$ be a probability measure on a measurable space $E$, let $H$ be a Markov kernel reversible with respect to $\pi$, let $f \in L^2_0(\pi)$, and let $X_0, X_1,\dots$ be the Markov chain with initial distribution $\pi$ and kernel $H$. Then the limit
--
--   $$
--   v(f, H) \;=\; \lim_{n\to\infty} \frac{1}{n}\operatorname{Var}_H\Bigl(\sum_{i=1}^{n} f(X_i)\Bigr)
--   $$
--
--   exists in $[0, \infty]$; it may be $+\infty$.
--
--   This justifies the definition of the asymptotic variance used in Theorem 4. By Kipnis and Varadhan (1986), a central limit theorem holds for $\sum f(X_i)$ when the limit is finite.
--
--   **Formalization Note** The variance is Mathlib's extended variance with values in $[0,\infty]$ and the division by $n$ is carried out in $[0,\infty]$; the term at $n = 0$ is $0/0 = 0$ and does not affect the limit. The page reads "The limit is guaranteed to exit", a misprint for "exist".
-- source:
--   L. Tierney, A Note on Metropolis–Hastings Kernels for General State Spaces, Ann. Appl. Probab. 8(1) (1998) 1–9, DOI 10.1214/aoap/1027961031, p. 6, proof of Theorem 4 (first sentence)

import Mathlib
import Definitions.Def_TierneyMH_Peskun_chainMeasure

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace TierneyMH.Peskun

/-- **Proof of Theorem 4** (Tierney 1998, p. 6): the limit defining the asymptotic variance
exists, possibly infinite. For a reversible Markov kernel `H` with invariant distribution `π`,
`f ∈ L²₀(π)` and the chain `X₀, X₁, …` started from `π`, the sequence
`(1/n) Var_H(∑_{i=1}^{n} f(X_i))` converges in `[0, ∞]`. The variance is Mathlib's
`ℝ≥0∞`-valued `evariance`, and the division is in `ℝ≥0∞`; its value at `n = 0` (`0 / 0 = 0`)
does not affect the limit. (The page says "guaranteed to exit", a slip for "exist".) -/
theorem asymptotic_variance_exists {E : Type*} [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π]
    (H : Kernel E E) [IsMarkovKernel H] (hH : Kernel.IsReversible H π)
    (f : E → ℝ) (hf_meas : Measurable f) (hf : MemLp f 2 π) (hf0 : ∫ x, f x ∂π = 0) :
    ∃ v : ℝ≥0∞, Tendsto (fun n : ℕ => evariance (pathSum f n) (chainMeasure π H) / n)
      atTop (𝓝 v) := by sorry

end TierneyMH.Peskun
