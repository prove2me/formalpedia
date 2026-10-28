-- Prove2me | Theorems.Thm_RobustSPA_Affiliated_proposition_2
-- name    : RobustSPA.Affiliated.proposition_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T08:28:49.607303+00:00
-- url     : https://prove2.me/theorems/88c6c56a-4028-4290-b304-4bca46b0f52d
-- title:
--   Proposition 2, p. 19 — (SPA(Φ*_n), F*_n) is a saddle point over 𝓕_aff, so 𝓡*_n(𝓕_aff) = 𝓡*_n(𝓕_iid)
-- statement:
--   Fix $n\ge 1$ buyers. Let $r^*_n\in(0,1/n)$ solve
--   $$(1-r)^{n-1}+\log r+\sum_{k=1}^{n-1}\frac{(1-r)^k}{k}=0 .$$
--   Let $m^*_n=\mathrm{SPA}(\Phi^*_n)$ be the second-price auction whose random reserve has the CDF $\Phi^*_n$ of Theorem 1. Let $F^*_n=G^{\otimes n}$ be the law of $n$ i.i.d. valuations with the isorevenue CDF $G(t)=1-r^*_n/t$ on $[r^*_n,1)$, $G=0$ below $r^*_n$ and $G=1$ from $1$ on (F-IsoRevenue). Then for every exchangeable and affiliated law $F$ on $[0,1]^n$ and every DSIC mechanism $m$,
--   $$R_n(m^*_n,F)\ \le\ R_n(m^*_n,F^*_n)\ \le\ R_n(m,F^*_n).$$
--   Consequently the minimax regret over exchangeable affiliated laws equals that over i.i.d. laws:
--   $$\mathcal R^*_n(\mathcal F_{\mathrm{aff}})=\mathcal R^*_n(\mathcal F_{\mathrm{iid}}).$$
--
--   The result shows that the minimax-regret optimal mechanism for i.i.d. valuations stays optimal when Nature may also correlate the valuations positively through affiliation. Allowing such dependence does not increase the seller's minimax regret.
--
--   **Formalization Note.** "$r^*_n$, $\Phi^*_n$ as given by Theorem 1" and "(F-IsoRevenue)" are restated as hypotheses, since Theorem 1 belongs to mission I and drafts cannot import drafts. The hypotheses are: $r$ lies in $(0,1/n)$ and solves the $r^*$-equation; $\rho$ is a probability law on $\mathbb R$ with CDF $\Phi^*_n$; $G$ is a probability law on $\mathbb R$ with the isorevenue CDF. They are satisfiable: Theorem 1 asserts that $r^*_n$ exists and that $\Phi^*_n$ is a CDF, and a law with the isorevenue CDF is constructed in the mission's sanity file. "Any mechanism $m$" means any $m$ in the DSIC class $\mathcal M$. The minimax regret is $\inf$ over DSIC mechanisms of $\sup$ over the class of the regret (2). $n=1$ is included.
-- source:
--   Anunrojwong, Balseiro & Besbes, On the Robustness of Second-Price Auctions in Prior-Independent Mechanism Design, arXiv:2204.10478v5, p. 19, Proposition 2 (with Theorem 1, p. 13, and (F-IsoRevenue), p. App-1)

import Mathlib
import Definitions.Def_RobustSPA_Affiliated_Setting

namespace RobustSPA.Affiliated

open MeasureTheory RobustSPA.IID

theorem proposition_2 (n : ℕ) (hn : 0 < n) (r : ℝ) (hr : r ∈ Set.Ioo (0 : ℝ) (1 / (n : ℝ)))
    (hrEq : rEq n r = 0) (ρ : ProbabilityMeasure ℝ) (hρ : ∀ t, cdfOf ρ t = PhiStar n r t)
    (G : ProbabilityMeasure ℝ) (hG : ∀ t, cdfOf G t = isoCDF r t) :
    (∀ μ ∈ Faff n, regret (SPA (ρ : Measure ℝ)) μ ≤
        regret (SPA (ρ : Measure ℝ)) (Measure.pi fun _ : Fin n => (G : Measure ℝ))) ∧
    (∀ m : Mechanism n, m.IsDSIC →
        regret (SPA (ρ : Measure ℝ)) (Measure.pi fun _ : Fin n => (G : Measure ℝ)) ≤
          regret m (Measure.pi fun _ : Fin n => (G : Measure ℝ))) ∧
    minimaxRegret n (Faff n) = minimaxRegret n (Fiid n) := by sorry

end RobustSPA.Affiliated
