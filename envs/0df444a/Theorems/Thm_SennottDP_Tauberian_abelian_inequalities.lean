-- Prove2me | Theorems.Thm_SennottDP_Tauberian_abelian_inequalities
-- name    : SennottDP.Tauberian.abelian_inequalities
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T13:08:22.14786+00:00
-- url     : https://prove2.me/theorems/ef290cc2-19d1-4012-b6ae-ada9730cd04d
-- title:
--   Eq. (A.28) — liminf w_n/n ≤ liminf (1−α)U(α) ≤ limsup (1−α)U(α) ≤ limsup w_n/n
-- statement:
--   Let $u_n \in [0,\infty]$ with $u_0 < \infty$, let $U(\alpha) = \sum_n \alpha^n u_n$ and $w_n = \sum_{k=0}^{n-1} u_k$. Then
--   $$\liminf_{n\to\infty} \frac{w_n}{n} \le \liminf_{\alpha\to 1^-} (1-\alpha)U(\alpha) \le \limsup_{\alpha\to 1^-} (1-\alpha)U(\alpha) \le \limsup_{n\to\infty} \frac{w_n}{n},$$
--   all four quantities being taken in $[0,\infty]$.
--
--   This is the Abelian half of Theorem A.4.2: the Abel means oscillate no more than the Cesàro means. In particular, if $w_n/n$ converges, so does $(1-\alpha)U(\alpha)$, to the same limit.
--
--   **Formalization Note** $\alpha \to 1^-$ is the filter of left neighbourhoods of $1$ in $\mathbb{R}_{\ge 0}$; $\liminf$ and $\limsup$ are those of the complete lattice $[0,\infty]$.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 282, Theorem A.4.2, (A.28); proof pp. 282–284

import Mathlib
import Definitions.Def_SennottDP_Tauberian_PowerSeries

open scoped ENNReal NNReal Topology
open Filter

namespace SennottDP.Tauberian

/-- Sennott (1999), p. 282, Theorem A.4.2, inequalities (A.28): for nonnegative terms
`u_n ∈ [0, ∞]` with `u_0 < ∞` and `w_n = ∑_{k<n} u_k`,
`lim inf_n w_n/n ≤ lim inf_{α→1⁻} (1−α)U(α) ≤ lim sup_{α→1⁻} (1−α)U(α) ≤ lim sup_n w_n/n`,
all four quantities taken in `[0, ∞]`. -/
theorem abelian_inequalities (u : ℕ → ℝ≥0∞) (hu0 : u 0 ≠ ⊤) :
    liminf (cesaroMean u) atTop ≤ liminf (abelMean u) (𝓝[<] (1 : ℝ≥0)) ∧
      liminf (abelMean u) (𝓝[<] (1 : ℝ≥0)) ≤ limsup (abelMean u) (𝓝[<] (1 : ℝ≥0)) ∧
      limsup (abelMean u) (𝓝[<] (1 : ℝ≥0)) ≤ limsup (cesaroMean u) atTop := by sorry

end SennottDP.Tauberian
