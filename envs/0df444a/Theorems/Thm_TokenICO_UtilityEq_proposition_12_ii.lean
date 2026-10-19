-- Prove2me | Theorems.Thm_TokenICO_UtilityEq_proposition_12_ii
-- name    : TokenICO.UtilityEq.proposition_12_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:27:36.582982+00:00
-- url     : https://prove2.me/theorems/d091efcd-6262-4b81-bc72-261ca6fb5a15
-- title:
--   Proposition 12(ii) — unique production-regime switch
-- statement:
--   Under the technical condition on the demand density and $v>2c$, there is a unique switch cap $\hat n\in(mc/v,m/2)$. For $n\in(mc/v,\hat n)$, the positive participation-boundary price is the unique positive solution of
--
--   $$\tau^*(n)=\frac vm\mathbb E\!\left[\min\left\{D,\frac{\tau^*(n)n}{c}\right\}\right].$$
--
--   For $n\in[\hat n,m(1-c/v))$, that price equals $(v/m)\mathbb E[\min\{D,F^{-1}(1-cm/((m-n)v))\}]$. The switch separates budget-limited from unconstrained production.
--
--   **Formalization Note** The printed endpoints $mc/v$ and $m(1-c/v)$ are excluded where the positive boundary price does not exist. “Unique solution” means unique positive solution because zero also satisfies the first equation. Utility at the price is evaluated at full participation.
-- source:
--   Gan, Tsoukalas & Netessine, Initial Coin Offerings, Speculation and Asset Tokenization, SSRN 3361121 (June 29, 2020), p. 34, Proposition 12(ii)

import Mathlib
import Definitions.Def_TokenICO_UtilityEq_Setting

open MeasureTheory ProbabilityTheory

namespace TokenICO.UtilityEq

/-- Proposition 12(ii), p. 34: the unique cap at which the optimal-price
formula switches production regimes. -/
theorem proposition_12_ii (m c v z : ℝ) (μ : Measure ℝ) (f f' : ℝ → ℝ)
    (h : Standing m c v z μ f f')
    (ht : TechCond c v μ f f')
    (Qr : ℝ → ℝ → ℝ) (hQr : ProdOptimal m c v μ Qr) :
    2 * c < v →
      ∃! nh : ℝ, nh ∈ Set.Ioo (m * c / v) (m / 2) ∧
        IsSwitch m c v z μ Qr nh := by sorry

end TokenICO.UtilityEq
