-- Prove2me | Theorems.Thm_SennottDP_Tauberian_abel_limit_r
-- name    : SennottDP.Tauberian.abel_limit_r
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T13:25:26.495468+00:00
-- url     : https://prove2.me/theorems/0c2360b8-037a-4ac9-9d2a-c383f7c9dab5
-- title:
--   Eq. (A.35) for f = r — (1−α)Σα^n u_n r(α^n) → L ∫_0^1 r
-- statement:
--   Let $u_n \in [0,\infty]$ with $u_0 < \infty$, suppose that $\lim_{\alpha\to 1^-} (1-\alpha)U(\alpha) = L < \infty$, and let $r$ be the function of Fig. A.1. Then
--   $$\lim_{\alpha\to 1^-} (1-\alpha)\sum_{n=0}^{\infty} \alpha^n u_n\, r(\alpha^n) = L\int_0^1 r(x)\,dx.$$
--
--   Since $\alpha^n r(\alpha^n) = 1$ exactly when $n \le (-\ln\alpha)^{-1}$ and $0$ otherwise, the left side is $(1-\alpha) w_{\lfloor (-\ln\alpha)^{-1}\rfloor + 1}$ (Eq. (A.40)); this is the last step of Karamata's proof.
--
--   **Formalization Note** The values $r(\alpha^n) \ge 0$ enter the $[0,\infty]$-valued series through `ENNReal.ofReal`, and the real integral $\int_0^1 r$ likewise.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 285, Eq. (A.35) for the function r, and (A.40)

import Mathlib
import Definitions.Def_SennottDP_Tauberian_PowerSeries
import Definitions.Def_SennottDP_Tauberian_KaramataR

open scoped ENNReal NNReal Topology
open Filter

namespace SennottDP.Tauberian

/-- Sennott (1999), p. 285, Eq. (A.35) for `f = r` (Fig. A.1): if `u_n ∈ [0, ∞]`, `u_0 < ∞`, and
`lim_{α→1⁻} (1−α)U(α) = L < ∞`, then `lim_{α→1⁻} (1−α) ∑ α^n u_n r(α^n) = L ∫_0^1 r(x) dx`. -/
theorem abel_limit_r (u : ℕ → ℝ≥0∞) (hu0 : u 0 ≠ ⊤) (L : ℝ≥0∞) (hL : L ≠ ⊤)
    (hlim : Tendsto (abelMean u) (𝓝[<] (1 : ℝ≥0)) (𝓝 L)) :
    Tendsto (fun α : ℝ≥0 =>
        (1 - (α : ℝ≥0∞)) * ∑' n : ℕ, (α : ℝ≥0∞) ^ n * u n * ENNReal.ofReal (r ((α : ℝ) ^ n)))
      (𝓝[<] (1 : ℝ≥0)) (𝓝 (L * ENNReal.ofReal (∫ x in (0 : ℝ)..1, r x))) := by sorry

end SennottDP.Tauberian
