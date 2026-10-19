-- Prove2me | Theorems.Thm_TokenICO_UtilityEq_proposition_2
-- name    : TokenICO.UtilityEq.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:27:44.308982+00:00
-- url     : https://prove2.me/theorems/7829a015-97e0-4b8c-ac51-a7b9ee236642
-- title:
--   Proposition 2 — conditions for a successful ICO
-- statement:
--   For a feasible cap $n\in[0,m]$, call the ICO successful when some positive price leads to positive token sales. In the utility-token model,
--
--   $$\bigl(\exists\tau>0:s^*(\tau,n)>0\bigr)\iff \frac{mc}{v}<n<m(1-c/v).$$
--
--   Consequently, some feasible cap can succeed if and only if $v>2c$. These are the critical-mass and price-cost conditions for positive fundraising.
--
--   **Formalization Note** The paper does not separately define “success.” This reads it as positive sales at a positive price, as in the proof on p. 39. The upper endpoint is open because production and participation vanish there.
-- source:
--   Gan, Tsoukalas & Netessine, Initial Coin Offerings, Speculation and Asset Tokenization, SSRN 3361121 (June 29, 2020), p. 13, Proposition 2

import Mathlib
import Definitions.Def_TokenICO_UtilityEq_Setting

open MeasureTheory ProbabilityTheory

namespace TokenICO.UtilityEq

/-- Proposition 2, p. 13: success at a fixed cap, and existence of any
successful design. -/
theorem proposition_2 (m c v z : ℝ) (μ : Measure ℝ) (f f' : ℝ → ℝ)
    (h : Standing m c v z μ f f') (Qr : ℝ → ℝ → ℝ)
    (hQr : ProdOptimal m c v μ Qr) :
    (∀ n : ℝ, 0 ≤ n → n ≤ m →
      ((∃ τ : ℝ, 0 < τ ∧ 0 < sstar m v z μ Qr τ n) ↔
        m * c / v < n ∧ n < m * (1 - c / v))) ∧
    ((∃ n : ℝ, 0 ≤ n ∧ n ≤ m ∧
      ∃ τ : ℝ, 0 < τ ∧ 0 < sstar m v z μ Qr τ n) ↔
      2 * c < v) := by sorry

end TokenICO.UtilityEq
