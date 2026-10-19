-- Prove2me | Theorems.Thm_TokenICO_UtilityEq_proposition_1
-- name    : TokenICO.UtilityEq.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:27:40.110712+00:00
-- url     : https://prove2.me/theorems/903dbd1a-35f1-4e5f-9f5a-bc5ff24d6f77
-- title:
--   Proposition 1 — optimal production in the funded subgame
-- statement:
--   Fix an ICO price $\tau\ge0$ and $s\in[0,m]$ tokens sold. Under the utility-token model, a quantity $Q$ is feasible and maximizes the firm's production-period objective if and only if
--
--   $$Q=\begin{cases}\min\!\left\{F^{-1}\!\left(1-\frac{m}{m-s}\frac cv\right),\frac{\tau s}{c}\right\},&0<s<m(1-c/v),\\0,&s=0\text{ or }s\ge m(1-c/v).\end{cases}$$
--
--   This identifies the unique optimal production quantity while preserving the ICO financing constraint.
--
--   **Formalization Note** The standing assumptions specify the demand law and a positive density on its interior. The production rule itself is defined through optimization, not through this formula.
-- source:
--   Gan, Tsoukalas & Netessine, Initial Coin Offerings, Speculation and Asset Tokenization, SSRN 3361121 (June 29, 2020), p. 11, Proposition 1

import Mathlib
import Definitions.Def_TokenICO_UtilityEq_Setting

open MeasureTheory ProbabilityTheory

namespace TokenICO.UtilityEq

/-- Proposition 1, p. 11: the two production regimes, including existence
and uniqueness of the maximizing quantity. -/
theorem proposition_1 (m c v z : ℝ) (μ : Measure ℝ) (f f' : ℝ → ℝ)
    (h : Standing m c v z μ f f') (τ s : ℝ)
    (hτ : 0 ≤ τ) (hs : 0 ≤ s) (hsm : s ≤ m) :
    ∀ Q : ℝ,
      (Q ∈ Set.Icc 0 (τ * s / c) ∧
        IsMaxOn (prodObj m c v μ s) (Set.Icc 0 (τ * s / c)) Q) ↔
      Q = if 0 < s ∧ s < m * (1 - c / v)
        then min (Finv μ (1 - m / (m - s) * (c / v))) (τ * s / c)
        else 0 := by sorry

end TokenICO.UtilityEq
