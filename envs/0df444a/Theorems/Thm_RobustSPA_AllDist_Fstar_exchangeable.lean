-- Prove2me | Theorems.Thm_RobustSPA_AllDist_Fstar_exchangeable
-- name    : RobustSPA.AllDist.Fstar_exchangeable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:28:39.347011+00:00
-- url     : https://prove2.me/theorems/32d09a04-9bad-4f75-b4ec-10d4334becf9
-- title:
--   Proposition 4, p. 22 — the uniform mixture F* = (1/n) Σ_k F*,k is exchangeable
-- statement:
--   Let $n \ge 1$ and let $G$ be a probability distribution supported on $[0,1]$. Let $\mathbf F^* = \frac1n\sum_{k=1}^n \mathbf F^{*,k}$, where $\mathbf F^{*,k}$ is the law of $t\,e_k$ with $t \sim G$. Then
--   $$\mathbf F^* \in \mathcal F_{\mathrm{exc}},$$
--   that is, $\mathbf F^*$ is a probability distribution on $[0,1]^n$ that is invariant under every permutation of the buyers.
--
--   The worst case of Proposition 4 is not i.i.d., but it is exchangeable; this is why the minimax regret over exchangeable laws and over all laws coincide.
--
--   **Formalization Note** Exchangeability is invariance of the law under $v \mapsto v \circ \sigma$ for every permutation $\sigma$ of the buyers. Proposition 4 applies this with $G$ the isorevenue law on $[1/e, 1]$.
-- source:
--   Anunrojwong, Balseiro & Besbes, On the Robustness of Second-Price Auctions in Prior-Independent Mechanism Design, arXiv:2204.10478v5, p. 22, Proposition 4 ("because F* is exchangeable")

import Mathlib
import Definitions.Def_RobustSPA_AllDist_Setting
open MeasureTheory

namespace RobustSPA.AllDist

/-- p. 22: `F*` is exchangeable (and supported on `[0,1]ⁿ`). -/
theorem Fstar_exchangeable (n : ℕ) (hn : 0 < n) (G : ProbabilityMeasure ℝ)
    (hG : (G : Measure ℝ) (Set.Icc 0 1)ᶜ = 0) :
    Fstar n (G : Measure ℝ) ∈ Fexc n := by sorry

end RobustSPA.AllDist
