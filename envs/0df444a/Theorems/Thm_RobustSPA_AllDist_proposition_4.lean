-- Prove2me | Theorems.Thm_RobustSPA_AllDist_proposition_4
-- name    : RobustSPA.AllDist.proposition_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T08:28:44.726864+00:00
-- url     : https://prove2.me/theorems/041bde22-0442-47f8-b63a-e920c52a2775
-- title:
--   Proposition 4, p. 22 — (SPA(Φ*), F*) is a saddle point and R*_n(𝓕_exc) = R*_n(𝓕_all) = R_n(m*, F*) = 1/e for every n
-- statement:
--   Let $n \ge 1$ buyers have valuations in $[0,1]$. For each $k$, let $\mathbf F^{*,k}$ be the law on $[0,1]^n$ under which $v_i = 0$ for $i \ne k$ and $v_k$ follows the **isorevenue** distribution on $[1/e, 1]$:
--   $$F^{*,k}(v_k) = \begin{cases} 0 & v_k \in [0, 1/e],\\ 1 - \dfrac{1}{e v_k} & v_k \in [1/e, 1),\\ 1 & v_k = 1,\end{cases}$$
--   and let $\mathbf F^* = \frac1n\sum_{k=1}^n \mathbf F^{*,k}$ be their uniform mixture. Let $m^* = \mathrm{SPA}(\Phi^*)$ be the second-price auction whose random reserve has CDF $\Phi^*(p) = \log p + 1$ on $[1/e, 1]$ (and $0$ below $1/e$, $1$ above $1$). Then, for every DSIC mechanism $m \in \mathcal M$ and every distribution $\mathbf F \in \mathcal F_{\mathrm{all}}$,
--   $$R_n(m^*, \mathbf F) \le R_n(m^*, \mathbf F^*) \le R_n(m, \mathbf F^*).$$
--   Moreover $\mathbf F^*$ is exchangeable, and
--   $$\mathcal R^*_n(\mathcal F_{\mathrm{exc}}) = \mathcal R^*_n(\mathcal F_{\mathrm{all}}) = R_n(m^*, \mathbf F^*) = \frac1e.$$
--
--   The value does not depend on $n$: against arbitrary or merely exchangeable joint valuations, adding buyers does not help a seller who does not know the distribution, because Nature can concentrate all value in one randomly chosen buyer.
--
--   **Formalization Note** $R_n(m, \mathbf F)$ is the regret (2) and $\mathcal R^*_n$ the minimax regret (3) of the model file; $\mathcal M$ carries the disclosed measurability and bounded-payment additions, and "for any mechanism $m$" is read as $m \in \mathcal M$. The page prints $\Phi^*(p) = \log(v) + 1$; the statement uses $\log p + 1$. The laws $\Phi^*$ and the isorevenue law $G$ are given through their CDFs (both exist), and $\mathbf F^{*,k}$ is the push-forward of $G$ under $t \mapsto t\,e_k$. The page's case $v_k \in [0,1/e]$ and $v_k \in [1/e, 1)$ overlap at $1/e$, where both give $0$. The conjunct $\mathbf F^* \in \mathcal F_{\mathrm{exc}}$ makes the page's "because $\mathbf F^*$ is exchangeable" explicit.
-- source:
--   Anunrojwong, Balseiro & Besbes, On the Robustness of Second-Price Auctions in Prior-Independent Mechanism Design, arXiv:2204.10478v5, p. 22, Proposition 4; proof pp. App-7–8

import Mathlib
import Definitions.Def_RobustSPA_AllDist_Setting
open MeasureTheory

namespace RobustSPA.AllDist

/-- Proposition 4, p. 22: `(SPA(Φ*), F*)` is a saddle point, and
`R*_n(𝓕_exc) = R*_n(𝓕_all) = R_n(m*, F*) = 1/e`. -/
theorem proposition_4 (n : ℕ) (hn : 0 < n) (ρ : ProbabilityMeasure ℝ)
    (hρ : ∀ t, cdfOf ρ t = PhiE t) (G : ProbabilityMeasure ℝ)
    (hG : ∀ t, cdfOf G t = isoCDF (Real.exp (-1)) t) :
    (∀ μ ∈ Fall n, regret (SPA (ρ : Measure ℝ)) μ
        ≤ regret (SPA (ρ : Measure ℝ)) (Fstar n (G : Measure ℝ))) ∧
    (∀ m : Mechanism n, m.IsDSIC →
        regret (SPA (ρ : Measure ℝ)) (Fstar n (G : Measure ℝ)) ≤ regret m (Fstar n (G : Measure ℝ))) ∧
    Fstar n (G : Measure ℝ) ∈ Fexc n ∧
    regret (SPA (ρ : Measure ℝ)) (Fstar n (G : Measure ℝ)) = Real.exp (-1) ∧
    minimaxRegret n (Fexc n) = Real.exp (-1) ∧
    minimaxRegret n (Fall n) = Real.exp (-1) := by sorry

end RobustSPA.AllDist
