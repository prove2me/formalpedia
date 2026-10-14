-- Prove2me | Theorems.Thm_RobustSPA_IID_theorem_1
-- name    : RobustSPA.IID.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:13:56.089244+00:00
-- url     : https://prove2.me/theorems/cd14d104-4a40-4793-86b9-3b2279745429
-- title:
--   Theorem 1, pp. 13–14 — SPA with random reserve Φ*_n is minimax-regret optimal against i.i.d. valuations; 𝓡*_n(𝓕_iid) = (1−r*_n)^{n−1} − ∫_{r*_n}^1 (1−r*_n/v)^{n−1} dv
-- statement:
--   A seller sells one item to $n \ge 1$ buyers whose valuations are i.i.d. with an unknown marginal supported on $[0,1]$, and measures a DSIC mechanism $m$ by its worst-case regret $\sup_{F \in \mathcal F_{\mathrm{iid}}} \mathbb E_F[\max(v) - \sum_i p_i(v)]$.
--
--   Let $r^*_n$ be the solution of
--   $$(1-r^*)^{n-1} + \log(r^*) + \sum_{k=1}^{n-1}\frac{(1-r^*)^k}{k} = 0;$$
--   it lies in $(0, 1/n)$ and is the only solution in $(0,1)$. Let
--   $$\Phi^*_n(v) = \Big(\frac{v}{v-r^*_n}\Big)^{n-1}\log\Big(\frac{v}{r^*_n}\Big) - \sum_{k=1}^{n-1}\frac1k\Big(\frac{v}{v-r^*_n}\Big)^{n-1-k}, \qquad v \in (r^*_n, 1].$$
--   Then there is a probability distribution on $[r^*_n, 1]$ with cumulative distribution function $\Phi^*_n$, and the second-price auction with random reserve price drawn from it is an optimal mechanism of the minimax regret problem:
--
--   1. it is DSIC;
--   2. its regret under every $F \in \mathcal F_{\mathrm{iid}}$ is at most $V_n$;
--   3. every DSIC mechanism has regret at least $V_n$ under some $F \in \mathcal F_{\mathrm{iid}}$;
--   4. the minimax regret is
--   $$\mathcal R^*_n(\mathcal F_{\mathrm{iid}}) = \inf_{m \in \mathcal M}\sup_{F \in \mathcal F_{\mathrm{iid}}} \mathrm{Regret}(m, F) = V_n := (1-r^*_n)^{n-1} - \int_{r^*_n}^1\Big(1 - \frac{r^*_n}{v}\Big)^{n-1}dv.$$
--
--   The result identifies, in quasi-closed form, the minimax-regret optimal mechanism over all DSIC mechanisms and its value, for every number of buyers; for $n = 1$ it recovers the Bergemann–Schlag value $1/e$.
--
--   **Formalization Note.** "The unique solution in $(0,1/n)$" is stated as a root in $(0,1/n)$ that is the only root in $(0,1)$ (what the proof on p. App-7 shows). "Optimal mechanism" is spelled out as items 1–3, and item 4 states (3) literally. The reserve law is any probability measure on $[r^*_n,1]$ with CDF $\Phi^*_n$ (defined as $0$ below $r^*_n$ and $1$ above $1$); its existence is part of the claim. DSIC is (IR), (IC), (AC) on $[0,1]^n$ with measurable rules and bounded payments; ties in the auction go to the lowest index.
-- source:
--   Anunrojwong, Balseiro & Besbes, On the Robustness of Second-Price Auctions in Prior-Independent Mechanism Design, arXiv:2204.10478v5, pp. 13–14, Theorem 1

import Mathlib
import Definitions.Def_RobustSPA_IID_Setting

namespace RobustSPA.IID

open MeasureTheory

/-- Theorem 1 (pp. 13–14). For `n ≥ 1` buyers with i.i.d. valuations on `[0,1]`, the equation
`(1 − r)^{n−1} + log r + Σ_{k=1}^{n−1} (1 − r)^k / k = 0` has a root `r*_n ∈ (0, 1/n)`, the only
root in `(0, 1)`; a second-price auction with random reserve drawn from a law on `[r*_n, 1]` with
CDF `Φ*_n` is DSIC and minimax-regret optimal, and the minimax regret is
`(1 − r*_n)^{n−1} − ∫_{r*_n}^1 (1 − r*_n/v)^{n−1} dv`. -/
theorem theorem_1 (n : ℕ) (hn : 0 < n) :
    ∃ r ∈ Set.Ioo (0 : ℝ) (1 / n), rEq n r = 0 ∧
      (∀ r' ∈ Set.Ioo (0 : ℝ) 1, rEq n r' = 0 → r' = r) ∧
      ∃ ρ : ProbabilityMeasure ℝ,
        (ρ : Measure ℝ) (Set.Icc r 1)ᶜ = 0 ∧
        (∀ t, cdfOf ρ t = PhiStar n r t) ∧
        (SPA (n := n) (ρ : Measure ℝ)).IsDSIC ∧
        (∀ μ ∈ Fiid n, regret (SPA (ρ : Measure ℝ)) μ ≤ value n r) ∧
        (∀ m : Mechanism n, m.IsDSIC → ∃ μ ∈ Fiid n, value n r ≤ regret m μ) ∧
        minimaxRegret n (Fiid n) = value n r := by sorry

end RobustSPA.IID
