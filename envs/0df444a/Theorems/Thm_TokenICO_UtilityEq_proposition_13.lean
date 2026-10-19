-- Prove2me | Theorems.Thm_TokenICO_UtilityEq_proposition_13
-- name    : TokenICO.UtilityEq.proposition_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:27:39.41429+00:00
-- url     : https://prove2.me/theorems/701a0dab-b828-4d14-87ac-dc5d91e6a3af
-- title:
--   Proposition 13 — unique optimal ICO cap
-- statement:
--   Suppose $v>2c$ and the Appendix B.1 demand condition holds. The unique optimal ICO cap $n^*\in(mc/v,m/2)$ equals the switch cap of Proposition 12(ii) and solves
--
--   $$\frac{vn^*}{cm}\mathbb E\!\left[\min\!\left\{D,F^{-1}\!\left(1-\frac{cm}{(m-n^*)v}\right)\right\}\right]=F^{-1}\!\left(1-\frac{cm}{(m-n^*)v}\right).$$
--
--   At the positive participation-boundary price, every other viable cap yields strictly less expected wealth. This identifies the firm's optimal design before the complete equilibrium statement.
--
--   **Formalization Note** The comparison runs over the open viable interval, since its printed upper endpoint has no positive boundary price. The source's $u(s^*(\tau,n))=0$ is read at full participation as $u(n)=0$.
-- source:
--   Gan, Tsoukalas & Netessine, Initial Coin Offerings, Speculation and Asset Tokenization, SSRN 3361121 (June 29, 2020), p. 35, Proposition 13 and (11)

import Mathlib
import Definitions.Def_TokenICO_UtilityEq_Setting

open MeasureTheory ProbabilityTheory

namespace TokenICO.UtilityEq

/-- Proposition 13, p. 35: the switch cap solves the printed equation
and uniquely maximizes wealth among viable caps at their optimal prices. -/
theorem proposition_13 (m c v z : ℝ) (μ : Measure ℝ) (f f' : ℝ → ℝ)
    (h : Standing m c v z μ f f')
    (ht : TechCond c v μ f f')
    (Qr : ℝ → ℝ → ℝ) (hQr : ProdOptimal m c v μ Qr) :
    2 * c < v →
      ∃ ns : ℝ,
        ns ∈ Set.Ioo (m * c / v) (m / 2) ∧
        IsSwitch m c v z μ Qr ns ∧
        v * ns / (c * m) *
          ES μ (Finv μ (1 - c * m / ((m - ns) * v))) =
          Finv μ (1 - c * m / ((m - ns) * v)) ∧
        ∀ n ∈ Set.Ioo (m * c / v) (m * (1 - c / v)),
          ∀ τ τs : ℝ,
            0 < τ → u m v z μ Qr τ n = 0 →
            0 < τs → u m v z μ Qr τs ns = 0 →
            n ≠ ns →
            wealth m c v z μ Qr τ n < wealth m c v z μ Qr τs ns := by sorry

end TokenICO.UtilityEq
