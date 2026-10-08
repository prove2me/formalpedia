-- Prove2me | Theorems.Thm_SmithRegenerative_Ergodic_lemma_7
-- name    : SmithRegenerative.Ergodic.lemma_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:41:10.458488+00:00
-- url     : https://prove2.me/theorems/1137a118-f4c9-420d-b4ab-cd0cce5e19c2
-- title:
--   Lemma 7 — i.i.d. x_n with E|x_n|^p < ∞ satisfy x_n/n^{1/p} → 0 with probability one
-- statement:
--   Let $x_1, x_2, \dots$ be independent, identically distributed real random variables, and let $p > 0$ be such that $E|x_1|^p < \infty$. Then, with probability one,
--   $$\lim_{n \to \infty} \frac{x_n}{n^{1/p}} = 0 .$$
--
--   In the mission this controls the size of a single cycle's contribution: applied to the cycle variations $\tilde y_n$ it shows that one cycle is negligible against the time elapsed, which is the content of Lemma 8.
--
--   **Formalization Note** The power $n^{1/p}$ is the real power; at $n = 0$ the quotient is $0$, which does not affect the limit. The sequence is indexed from $1$ as in the paper; the value at index $0$ is unconstrained.
-- source:
--   Smith, Regenerative stochastic processes, Proc. R. Soc. Lond. A 232(1188):6–31 (1955), DOI 10.1098/rspa.1955.0198, p. 26, §5·3, Lemma 7

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology

namespace SmithRegenerative.Ergodic

/-- **Lemma 7** (Smith, *Regenerative stochastic processes*, Proc. R. Soc. Lond. A
232(1188):6–31 (1955), §5·3, p. 26): "If {x_n} (n = 1, 2, …), is a sequence of independent,
identically distributed random variables for which E|x_n|^p < ∞, (p > 0), then
lim_{n→∞} x_n/n^{1/p} = 0 with probability one."

Formalization Note: the paper's `x_1, x_2, …` are `x 1, x 2, …`; `x 0` is unconstrained and does
not affect the limit. Independence is mutual independence of `(x (n+1))_{n ≥ 0}`, identical
distribution is `IdentDistrib (x (n+1)) (x 1)`, and `E|x_n|^p < ∞` is integrability of
`|x_1|^p` (real power). `n^{1/p}` is `Real.rpow`; at `n = 0` it is `0` and the quotient is `0`,
which does not affect the limit. -/
theorem lemma_7 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (x : ℕ → Ω → ℝ) (p : ℝ) (hp : 0 < p)
    (hindep : iIndepFun (fun n : ℕ => x (n + 1)) P)
    (hident : ∀ n, IdentDistrib (x (n + 1)) (x 1) P P)
    (hmom : Integrable (fun ω => |x 1 ω| ^ p) P) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => x n ω / (n : ℝ) ^ (1 / p)) atTop (𝓝 0) := by sorry

end SmithRegenerative.Ergodic
