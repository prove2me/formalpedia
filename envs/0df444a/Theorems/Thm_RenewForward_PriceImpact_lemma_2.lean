-- Prove2me | Theorems.Thm_RenewForward_PriceImpact_lemma_2
-- name    : RenewForward.PriceImpact.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:19:03.073246+00:00
-- url     : https://prove2.me/theorems/d2b6ce8a-fc01-4339-af3b-fb611d35316e
-- title:
--   Lemma 2, p. 13 — each retailer's optimal forward position is unique, and the market clears exactly at the total position (10)
-- statement:
--   Under the standing assumptions, fix a wind capacity $k_W \ge 0$, a total forward sale $F$ of the producers and a forward price $p_f$, and let $p_s = (p_0 - F)/3$ be the Lemma 1 spot price. A retailer with demand share $\theta_{Ri} = \theta/N_R$ takes $p_f$ and the law of $p_s$ as given and chooses its forward position to maximize $U(\pi_{Ri}) = E[\pi_{Ri}] - \frac\lambda2 V(\pi_{Ri})$, with $\pi_{Ri} = p_R\theta_{Ri} - p_s(\theta_{Ri} - f_{Ri}) - p_f f_{Ri}$.
--
--   1. The retailer's optimal position exists, is unique, and equals
--   $$f_{Ri} = \frac{E[p_s] - p_f}{\lambda V(p_s)} - \frac{\mathrm{Cov}(p_R\theta_{Ri} - p_s\theta_{Ri},\, p_s)}{V(p_s)}.$$
--   2. Consequently the forward market clears at $(p_f, F)$ (optimal retailer positions summing to $F$ exist) if and only if
--   $$F = N_R\,\frac{E[p_s] - p_f}{\lambda V(p_s)} + \sum_{i=1}^{N_R} \frac{-\mathrm{Cov}(p_R\theta_{Ri} - p_s\theta_{Ri},\, p_s)}{V(p_s)}.$$
--
--   The first summand is the retailers' speculative *basis* term, the second their *hedging* term. Solving the clearing condition for $p_f$ gives the linear inverse forward demand the producers face.
--
--   **Formalization Note.** $V(p_s) > 0$ follows from $V(\theta) > 0$ and independence; it is not a separate hypothesis. The covariance is Mathlib's `covariance`.
-- source:
--   Peura & Bunn, Renewable power and electricity prices: The impact of forward markets, author-accepted manuscript, LBS Research Online eprint 1432 (Management Science 67(8), 2021, doi:10.1287/mnsc.2020.3710), p. 13, Lemma 2, (10)

import Mathlib
import Definitions.Def_RenewForward_PriceImpact_Setting

namespace RenewForward.PriceImpact

open MeasureTheory ProbabilityTheory

/-- Lemma 2 (Retailer hedging), p. 13: each price-taking retailer has a unique optimal forward position, and
the market clears at `(pf, F)` exactly when `F` equals the retailers' total position (10). -/
theorem lemma_2 (M : Params) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (θ ξ : Ω → ℝ) (hS : Standing M P θ ξ) (kW F pf : ℝ) (hkW : 0 ≤ kW) :
    (∀ fr : ℝ, IsRetailerOpt M P θ ξ kW F pf fr ↔
      fr = (∫ w, spotP M θ ξ kW F w ∂P - pf) / (M.lam * variance (spotP M θ ξ kW F) P)
        - covariance (fun w => M.pR * (θ w / M.NR) - spotP M θ ξ kW F w * (θ w / M.NR))
            (spotP M θ ξ kW F) P / variance (spotP M θ ξ kW F) P) ∧
    (Clears M P θ ξ kW pf F ↔
      F = M.NR * ((∫ w, spotP M θ ξ kW F w ∂P - pf) / (M.lam * variance (spotP M θ ξ kW F) P))
        + ∑ _i : Fin M.NR,
            -covariance (fun w => M.pR * (θ w / M.NR) - spotP M θ ξ kW F w * (θ w / M.NR))
              (spotP M θ ξ kW F) P / variance (spotP M θ ξ kW F) P) := by sorry

end RenewForward.PriceImpact
