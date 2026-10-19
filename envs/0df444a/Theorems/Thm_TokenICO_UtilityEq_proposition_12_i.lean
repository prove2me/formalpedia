-- Prove2me | Theorems.Thm_TokenICO_UtilityEq_proposition_12_i
-- name    : TokenICO.UtilityEq.proposition_12_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:27:36.290837+00:00
-- url     : https://prove2.me/theorems/0c635d46-ef0c-47aa-8cfa-e1aa73525962
-- title:
--   Proposition 12(i) — unique positive ICO price at a viable cap
-- statement:
--   Suppose $v>2c$ and fix a cap $n\in(mc/v,m(1-c/v))$. There is exactly one positive ICO price $\tau^*(n)$ at which the expected utility of a speculator, evaluated when all $n$ tokens sell, is zero:
--
--   $$\exists!\,\tau^*(n)>0:\quad u_{\tau^*(n)}(n)=0.$$
--
--   This price is the participation boundary used in the firm's cap decision.
--
--   **Formalization Note** The printed upper endpoint is closed, but no positive solution exists there. The printed $u(s^*(\tau^*(n)))=0$ is read as $u(n)=0$ at full participation; literal evaluation at zero sales would make the uniqueness claim false.
-- source:
--   Gan, Tsoukalas & Netessine, Initial Coin Offerings, Speculation and Asset Tokenization, SSRN 3361121 (June 29, 2020), p. 34, Proposition 12(i)

import Mathlib
import Definitions.Def_TokenICO_UtilityEq_Setting

open MeasureTheory ProbabilityTheory

namespace TokenICO.UtilityEq

/-- Proposition 12(i), p. 34: at each viable cap, a unique positive
ICO price exhausts the speculators' expected profit. -/
theorem proposition_12_i (m c v z : ℝ) (μ : Measure ℝ) (f f' : ℝ → ℝ)
    (h : Standing m c v z μ f f') (Qr : ℝ → ℝ → ℝ)
    (hQr : ProdOptimal m c v μ Qr) :
    2 * c < v →
      ∀ n ∈ Set.Ioo (m * c / v) (m * (1 - c / v)),
        ∃! τ : ℝ, 0 < τ ∧ u m v z μ Qr τ n = 0 := by sorry

end TokenICO.UtilityEq
