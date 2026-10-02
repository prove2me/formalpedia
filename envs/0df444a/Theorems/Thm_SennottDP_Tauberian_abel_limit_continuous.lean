-- Prove2me | Theorems.Thm_SennottDP_Tauberian_abel_limit_continuous
-- name    : SennottDP.Tauberian.abel_limit_continuous
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T13:22:19.378999+00:00
-- url     : https://prove2.me/theorems/bcb9e90d-83e0-4dda-bb61-73d0933fe7e9
-- title:
--   Eq. (A.35) for continuous f — (1−α)Σα^n u_n f(α^n) → L ∫_0^1 f
-- statement:
--   Let $u_n \in [0,\infty]$ with $u_0 < \infty$, and suppose that $\lim_{\alpha\to 1^-} (1-\alpha)U(\alpha) = L < \infty$. Let $f$ be a real function continuous on $[0,1]$ and set $U_f(\alpha) = \sum_{n=0}^{\infty} \alpha^n u_n f(\alpha^n)$. Then
--   $$\lim_{\alpha\to 1^-} (1-\alpha) U_f(\alpha) = L \int_0^1 f(x)\,dx.$$
--
--   This is the second step of Karamata's proof, passing from polynomials to continuous functions.
--
--   **Formalization Note** Under the hypothesis every $u_n$ is finite (a single infinite term would make $U(\alpha) = \infty$ for all $\alpha \in (0,1)$), so $U_f(\alpha)$ is written as a real series with the terms $u_n$ converted to real numbers; it converges absolutely for $\alpha$ near $1$. The book says only "continuous"; continuity on the closed interval $[0,1]$ is what the Weierstrass approximation (A.37) requires. The integral is the interval integral over $[0,1]$.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), pp. 284–285, Eqs. (A.34), (A.35), (A.37)–(A.39)

import Mathlib
import Definitions.Def_SennottDP_Tauberian_PowerSeries

open scoped ENNReal NNReal Topology
open Filter

namespace SennottDP.Tauberian

/-- Sennott (1999), p. 285, Eq. (A.35) for continuous functions: if `u_n ∈ [0, ∞]`, `u_0 < ∞`, and
`lim_{α→1⁻} (1−α)U(α) = L < ∞`, then for every real function `f` continuous on `[0, 1]`,
`lim_{α→1⁻} (1−α) U_f(α) = L ∫_0^1 f(x) dx`, where `U_f(α) = ∑ α^n u_n f(α^n)` (A.34).
(Under the hypothesis every `u_n` is finite, so `U_f` is a real series.) -/
theorem abel_limit_continuous (u : ℕ → ℝ≥0∞) (hu0 : u 0 ≠ ⊤) (L : ℝ≥0∞) (hL : L ≠ ⊤)
    (hlim : Tendsto (abelMean u) (𝓝[<] (1 : ℝ≥0)) (𝓝 L)) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc 0 1)) :
    Tendsto (fun α : ℝ≥0 =>
        (1 - (α : ℝ)) * ∑' n : ℕ, (α : ℝ) ^ n * (u n).toReal * f ((α : ℝ) ^ n))
      (𝓝[<] (1 : ℝ≥0)) (𝓝 (L.toReal * ∫ x in (0 : ℝ)..1, f x)) := by sorry

end SennottDP.Tauberian
