-- Prove2me | Theorems.Thm_TokenICO_UtilityEq_lemma_2_ii
-- name    : TokenICO.UtilityEq.lemma_2_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:27:37.120585+00:00
-- url     : https://prove2.me/theorems/f89bad5f-1495-4d23-a060-2c38383bb2ad
-- title:
--   Lemma 2(ii) — participation below the diversion threshold
-- statement:
--   At a positive ICO price $\tau$ and feasible cap $n$, let $s^*(\tau,n)$ be the number of participating speculators under the simultaneous-arrival rule. Then
--
--   $$0\le s^*(\tau,n)\le m(1-c/v),\qquad s^*(\tau,n)>0\Longrightarrow Q(\tau,s^*(\tau,n))>0.$$
--
--   Thus a positive sale cannot end in complete diversion of the proceeds.
--
--   **Formalization Note** The paper's statement omits $\tau>0$. At $\tau=0$, every cap is accepted while the production budget is zero, so this condition is needed for the printed conclusion. The production rule is optimal in every feasible subgame.
-- source:
--   Gan, Tsoukalas & Netessine, Initial Coin Offerings, Speculation and Asset Tokenization, SSRN 3361121 (June 29, 2020), p. 12, Lemma 2(ii)

import Mathlib
import Definitions.Def_TokenICO_UtilityEq_Setting

open MeasureTheory ProbabilityTheory

namespace TokenICO.UtilityEq

/-- Lemma 2(ii), p. 12: the participating speculators do not face
complete fund diversion at a positive ICO price. -/
theorem lemma_2_ii (m c v z : ℝ) (μ : Measure ℝ) (f f' : ℝ → ℝ)
    (h : Standing m c v z μ f f') (Qr : ℝ → ℝ → ℝ)
    (hQr : ProdOptimal m c v μ Qr) (τ n : ℝ)
    (hτ : 0 < τ) (hn : 0 ≤ n) (hnm : n ≤ m) :
    0 ≤ sstar m v z μ Qr τ n ∧
    sstar m v z μ Qr τ n ≤ m * (1 - c / v) ∧
    (0 < sstar m v z μ Qr τ n →
      0 < Qr τ (sstar m v z μ Qr τ n)) := by sorry

end TokenICO.UtilityEq
