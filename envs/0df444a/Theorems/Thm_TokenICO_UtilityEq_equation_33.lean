-- Prove2me | Theorems.Thm_TokenICO_UtilityEq_equation_33
-- name    : TokenICO.UtilityEq.equation_33
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:27:36.85496+00:00
-- url     : https://prove2.me/theorems/766ea1b3-63fa-4c7e-a09b-8d7e048e8c8e
-- title:
--   Equation (33) — the participation boundary maximizes wealth at a fixed cap
-- statement:
--   Suppose $v>2c$ and $n\in(mc/v,m(1-c/v))$. If $\tau^*>0$ makes speculator utility at full participation vanish, then it is the greatest nonnegative price with nonnegative utility and maximizes the firm's expected wealth over nonnegative prices at that cap:
--
--   $$\tau^*=\max\{\tau\ge0:u_\tau(n)\ge0\},\qquad \Pi(\tau,n)\le\Pi(\tau^*,n)\quad(\tau\ge0).$$
--
--   This connects the participation constraint to the firm's optimal ICO price.
--
--   **Formalization Note** The paper writes utility at $s^*(\tau,n)$ in (33). The positive boundary is characterized at full participation; at abstention the utility $u(0)$ is automatically zero. Equation (33) also equates utility with its margin while (1) multiplies the margin by $s/z$; at positive full participation the two have the same sign, which is what the maximum statement uses.
-- source:
--   Gan, Tsoukalas & Netessine, Initial Coin Offerings, Speculation and Asset Tokenization, SSRN 3361121 (June 29, 2020), p. 45, proof of Proposition 12(i), (33)

import Mathlib
import Definitions.Def_TokenICO_UtilityEq_Setting

open MeasureTheory ProbabilityTheory

namespace TokenICO.UtilityEq

/-- Equation (33) and its preceding optimal-price claim in the proof of
Proposition 12(i), p. 45. -/
theorem equation_33 (m c v z : ℝ) (μ : Measure ℝ) (f f' : ℝ → ℝ)
    (h : Standing m c v z μ f f') (Qr : ℝ → ℝ → ℝ)
    (hQr : ProdOptimal m c v μ Qr)
    (hv : 2 * c < v) (n τs : ℝ)
    (hn : n ∈ Set.Ioo (m * c / v) (m * (1 - c / v)))
    (hτ : 0 < τs) (hu : u m v z μ Qr τs n = 0) :
    IsGreatest {τ : ℝ | 0 ≤ τ ∧ 0 ≤ u m v z μ Qr τ n} τs ∧
    IsMaxOn (fun τ : ℝ => wealth m c v z μ Qr τ n) (Set.Ici 0) τs := by sorry

end TokenICO.UtilityEq
