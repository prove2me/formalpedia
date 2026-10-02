-- Prove2me | Theorems.Thm_SennottDP_Tauberian_tauberian_theorem
-- name    : SennottDP.Tauberian.tauberian_theorem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T13:31:40.142126+00:00
-- url     : https://prove2.me/theorems/58484811-f9ff-463b-87e3-09e8dc238c99
-- title:
--   Theorem A.4.2 — Abel and Cesàro means of a nonnegative series: (A.28) and the Tauberian equivalence
-- statement:
--   Let $u_n \in [0,\infty]$ be nonnegative terms with $u_0 < \infty$, let $U(\alpha) = \sum_{n=0}^{\infty} \alpha^n u_n$ be their power series, and let $w_n = \sum_{k=0}^{n-1} u_k$ for $n \ge 1$. Then
--   $$\liminf_{n\to\infty} \frac{w_n}{n} \le \liminf_{\alpha\to 1^-} (1-\alpha)U(\alpha) \le \limsup_{\alpha\to 1^-} (1-\alpha)U(\alpha) \le \limsup_{n\to\infty} \frac{w_n}{n}. \tag{A.28}$$
--   Moreover the following statements are equivalent:
--
--   1. all the terms in (A.28) are equal and finite;
--   2. $\lim_{n\to\infty} w_n/n$ exists and is finite;
--   3. $\lim_{\alpha\to 1^-} (1-\alpha)U(\alpha)$ exists and is finite.
--
--   The implication from 3 to 2 is the Tauberian direction: for nonnegative terms, convergence of the Abel means forces convergence of the Cesàro means, with no further growth condition. In the theory of Markov decision chains this links the discounted cost criterion ($\alpha \to 1^-$) with the average cost criterion.
--
--   **Formalization Note** All quantities are in $[0,\infty]$; $\liminf$/$\limsup$ are those of the complete lattice $[0,\infty]$, $\alpha \to 1^-$ is the filter of left neighbourhoods of $1$ in $\mathbb{R}_{\ge 0}$, and $n \to \infty$ is `atTop` on $\mathbb{N}$ (the value of $w_n/n$ at $n = 0$ is irrelevant). "Exists and is finite" is $\exists L \ne \infty$ with convergence to $L$ in $[0,\infty]$. The equivalence is stated as `List.TFAE`.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 282, Theorem A.4.2, (A.28); proof pp. 282–286

import Mathlib
import Definitions.Def_SennottDP_Tauberian_PowerSeries

open scoped ENNReal NNReal Topology
open Filter

namespace SennottDP.Tauberian

/-- Sennott (1999), p. 282, Theorem A.4.2. Let `u_n ∈ [0, ∞]` with `u_0 < ∞`, `U(α) = ∑ α^n u_n`
(A.20) and `w_n = ∑_{k=0}^{n-1} u_k`. Then (A.28)
`lim inf_n w_n/n ≤ lim inf_{α→1⁻} (1−α)U(α) ≤ lim sup_{α→1⁻} (1−α)U(α) ≤ lim sup_n w_n/n`,
and the following are equivalent: (i) all the terms in (A.28) are equal and finite;
(ii) `lim_n w_n/n` exists and is finite; (iii) `lim_{α→1⁻} (1−α)U(α)` exists and is finite. -/
theorem tauberian_theorem (u : ℕ → ℝ≥0∞) (hu0 : u 0 ≠ ⊤) :
    (liminf (cesaroMean u) atTop ≤ liminf (abelMean u) (𝓝[<] (1 : ℝ≥0)) ∧
      liminf (abelMean u) (𝓝[<] (1 : ℝ≥0)) ≤ limsup (abelMean u) (𝓝[<] (1 : ℝ≥0)) ∧
      limsup (abelMean u) (𝓝[<] (1 : ℝ≥0)) ≤ limsup (cesaroMean u) atTop) ∧
    List.TFAE
      [liminf (cesaroMean u) atTop = liminf (abelMean u) (𝓝[<] (1 : ℝ≥0)) ∧
          liminf (abelMean u) (𝓝[<] (1 : ℝ≥0)) = limsup (abelMean u) (𝓝[<] (1 : ℝ≥0)) ∧
          limsup (abelMean u) (𝓝[<] (1 : ℝ≥0)) = limsup (cesaroMean u) atTop ∧
          limsup (cesaroMean u) atTop ≠ ⊤,
        ∃ L : ℝ≥0∞, L ≠ ⊤ ∧ Tendsto (cesaroMean u) atTop (𝓝 L),
        ∃ L : ℝ≥0∞, L ≠ ⊤ ∧ Tendsto (abelMean u) (𝓝[<] (1 : ℝ≥0)) (𝓝 L)] := by sorry

end SennottDP.Tauberian
