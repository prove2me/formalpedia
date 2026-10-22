-- Prove2me | Theorems.Thm_SpecActionsProb_Latency_proposition_1
-- name    : SpecActionsProb.Latency.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:17:27.043953+00:00
-- url     : https://prove2.me/theorems/17609a0b-0557-46ea-a864-49cf9d95ff44
-- title:
--   Proposition 1 — exact expected runtime ratio and limit
-- statement:
--   Suppose each of $k$ independent branches is correct with probability $0<p\le1$, the speculator latency has rate $\alpha$, and the real-call latency has rate $0<\beta<\alpha$. All guesses and latencies are mutually independent. Put $p(k)=1-(1-p)^k$. For every horizon $T\ge1$, the expected runtimes of the Appendix A speculative and sequential executions satisfy
--
--   $$\frac{\mathbb E[T_s]}{\mathbb E[T_{\mathrm{seq}}]}=1-\frac1T\frac{\alpha}{\alpha+\beta}\left[\frac{(T-1)p(k)}{1+p(k)}+\frac{p(k)^2}{(1+p(k))^2}-\frac{p(k)^2}{(1+p(k))^2}(-p(k))^{T-1}\right].$$
--
--   As $T\to\infty$, this ratio converges to $1-\frac{p(k)}{1+p(k)}\frac{\alpha}{\alpha+\beta}$. The result identifies the finite-horizon and limiting latency savings for an execution model built from random calls.
--
--   **Formalization Note** The ratio uses integrals of the random runtimes, not expressions defined to equal those integrals. The restriction $T\ge1$ makes the denominator positive. Windows use zero-based indices; a hit costs $\min(A_t,B_t)+B_{t+1}$ and consumes the following window. The page's $\beta<\alpha$ and $p>0$ hypotheses are retained. Concurrency without interference and negligible transition and parameter-construction costs are part of the runtime model.
-- source:
--   Ye et al., Speculative Actions: A Lossless Framework for Faster Agentic Systems, arXiv:2510.04371v2, p. 5, Proposition 1; Appendix A, pp. 14–15

import Mathlib
import Definitions.Def_SpecActionsProb_Latency_Model

set_option autoImplicit false

namespace SpecActionsProb.Latency

open MeasureTheory ProbabilityTheory

/-- Proposition 1, p. 5: exact finite horizon ratio and its limit for the random runtimes. -/
theorem proposition_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (k : ℕ) (α β p : ℝ) (hβ : 0 < β) (hβα : β < α) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (X : Idx k → Ω → ℝ) (hX : IsSpecModel P k α β p X) :
    let pk : ℝ := 1 - (1 - p) ^ k
    (∀ T : ℕ, 1 ≤ T →
      (∫ ω, specRuntime X T ω ∂P) / (∫ ω, seqRuntime X T ω ∂P)
        = 1 - 1 / (T : ℝ) * (α / (α + β)) *
            (((T : ℝ) - 1) * pk / (1 + pk) + pk ^ 2 / (1 + pk) ^ 2
              - pk ^ 2 / (1 + pk) ^ 2 * (-pk) ^ (T - 1))) ∧
    Filter.Tendsto (fun T : ℕ => (∫ ω, specRuntime X T ω ∂P) / (∫ ω, seqRuntime X T ω ∂P))
      Filter.atTop (nhds (1 - pk / (1 + pk) * (α / (α + β)))) := by sorry

end SpecActionsProb.Latency
