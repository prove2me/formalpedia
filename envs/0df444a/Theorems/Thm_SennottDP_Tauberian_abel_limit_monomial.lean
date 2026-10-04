-- Prove2me | Theorems.Thm_SennottDP_Tauberian_abel_limit_monomial
-- name    : SennottDP.Tauberian.abel_limit_monomial
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T13:16:58.711844+00:00
-- url     : https://prove2.me/theorems/fa8368f5-4d8b-459a-8298-726d8b8e6516
-- title:
--   Eqs. (A.35)–(A.36) — Karamata's step for monomials: (1−α)Σα^n u_n α^{kn} → L/(k+1)
-- statement:
--   Let $u_n \in [0,\infty]$ with $u_0 < \infty$, and suppose that the Abel means converge to a finite limit:
--   $$\lim_{\alpha\to 1^-} (1-\alpha)U(\alpha) = L < \infty.$$
--   Then for every natural number $k$, with $f(x) = x^k$ and $U_f(\alpha) = \sum_n \alpha^n u_n f(\alpha^n)$,
--   $$\lim_{\alpha\to 1^-} (1-\alpha)\sum_{n=0}^{\infty} \alpha^n u_n (\alpha^n)^k = L\int_0^1 x^k\,dx = \frac{L}{k+1}.$$
--
--   This is the first step of Karamata's proof: relation (A.35) holds for monomials, hence by linearity for polynomials.
--
--   **Formalization Note** Sums and the limit are in $[0,\infty]$; $L/(k+1)$ is $[0,\infty]$ division by the positive integer $k+1$. The case $k = 0$ is the hypothesis itself; the book writes the step for positive $k$.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), pp. 284–285, Eqs. (A.34)–(A.36)

import Mathlib
import Definitions.Def_SennottDP_Tauberian_PowerSeries

open scoped ENNReal NNReal Topology
open Filter

namespace SennottDP.Tauberian

/-- Sennott (1999), pp. 284–285, Eqs. (A.35)–(A.36) for `f(x) = x^k`: if `u_n ∈ [0, ∞]`,
`u_0 < ∞`, and `lim_{α→1⁻} (1−α)U(α) = L < ∞`, then
`lim_{α→1⁻} (1−α) ∑ α^n u_n (α^n)^k = L ∫_0^1 x^k dx = L/(k+1)`. -/
theorem abel_limit_monomial (u : ℕ → ℝ≥0∞) (hu0 : u 0 ≠ ⊤) (L : ℝ≥0∞) (hL : L ≠ ⊤)
    (hlim : Tendsto (abelMean u) (𝓝[<] (1 : ℝ≥0)) (𝓝 L)) (k : ℕ) :
    Tendsto (fun α : ℝ≥0 =>
        (1 - (α : ℝ≥0∞)) * ∑' n : ℕ, (α : ℝ≥0∞) ^ n * u n * ((α : ℝ≥0∞) ^ n) ^ k)
      (𝓝[<] (1 : ℝ≥0)) (𝓝 (L / ((k : ℝ≥0∞) + 1))) := by sorry

end SennottDP.Tauberian
