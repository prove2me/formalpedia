-- Prove2me | Theorems.Thm_TokenICO_UtilityEq_proposition_3
-- name    : TokenICO.UtilityEq.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:27:41.943182+00:00
-- url     : https://prove2.me/theorems/71dc24ef-189e-49ec-97fb-e9a28dcbe735
-- title:
--   Proposition 3 — failure threshold and unique utility-token equilibrium
-- statement:
--   In the utility-token model, if customer value satisfies $v\le2c$, no feasible ICO price and cap raises cash. If $v>2c$, an equilibrium exists and every equilibrium has the same price $\tau^*$ and cap $n^*$. Its cap lies in $(mc/v,m/2)$ and is the unique cap in that interval satisfying
--
--   $$\frac{vn^*}{cm}\mathbb E[\min\{D,Q^*\}]=Q^*,\qquad Q^*=F^{-1}\!\left(1-\frac{m}{m-n^*}\frac cv\right).$$
--
--   The ICO price is $\tau^*=(v/m)\mathbb E[\min\{D,Q^*\}]$. At every equilibrium, all $n^*$ tokens sell, production equals $Q^*$, and production cost uses all ICO proceeds: $cQ^*=\tau^*n^*$. In the market period the token price is $(v/m)\min\{Q^*,D\}$ and its expectation equals $\tau^*$.
--
--   This gives both the success threshold and the firm's unique optimal ICO design under moral hazard.
--
--   **Formalization Note** The density regularity and Appendix B.1 condition are included because the paper's uniqueness proof uses them. “Fails” means no cash is raised at any feasible design. Uniqueness concerns $(\tau,n)$; production is pinned at the equilibrium history for every optimal production rule. Quantities and token counts are real.
-- source:
--   Gan, Tsoukalas & Netessine, Initial Coin Offerings, Speculation and Asset Tokenization, SSRN 3361121 (June 29, 2020), pp. 13–14, Proposition 3(i)–(ii)(a)–(f)

import Mathlib
import Definitions.Def_TokenICO_UtilityEq_Setting

open MeasureTheory ProbabilityTheory

namespace TokenICO.UtilityEq

/-- Proposition 3, pp. 13–14: failure below the value-cost threshold,
and the unique utility-token equilibrium above it, including (a)–(f). -/
theorem proposition_3 (m c v z : ℝ) (μ : Measure ℝ) (f f' : ℝ → ℝ)
    (h : Standing m c v z μ f f')
    (ht : TechCond c v μ f f') :
    (v ≤ 2 * c →
      ∀ Qr : ℝ → ℝ → ℝ, ProdOptimal m c v μ Qr →
        ∀ τ n : ℝ, 0 ≤ τ → 0 ≤ n → n ≤ m →
          τ * sstar m v z μ Qr τ n = 0) ∧
    (2 * c < v →
      ∃ τs ns : ℝ,
        (∃ Qr : ℝ → ℝ → ℝ, IsEquilibrium m c v z μ Qr τs ns) ∧
        (∀ Qr : ℝ → ℝ → ℝ, ∀ τ n : ℝ,
          IsEquilibrium m c v z μ Qr τ n → τ = τs ∧ n = ns) ∧
        ns ∈ Set.Ioo (m * c / v) (m / 2) ∧
        v * ns / (c * m) * ES μ (Qcap m c v μ ns) = Qcap m c v μ ns ∧
        (∀ n ∈ Set.Ioo (m * c / v) (m / 2),
          v * n / (c * m) * ES μ (Qcap m c v μ n) = Qcap m c v μ n →
            n = ns) ∧
        τs = v / m * ES μ (Qcap m c v μ ns) ∧
        (∀ Qr : ℝ → ℝ → ℝ,
          IsEquilibrium m c v z μ Qr τs ns →
            Qr τs (sstar m v z μ Qr τs ns) = Qcap m c v μ ns ∧
            sstar m v z μ Qr τs ns = ns ∧
            c * Qr τs (sstar m v z μ Qr τs ns) =
              τs * sstar m v z μ Qr τs ns) ∧
        (∫ x, v / m * min (Qcap m c v μ ns) x ∂μ) = τs) := by sorry

end TokenICO.UtilityEq
