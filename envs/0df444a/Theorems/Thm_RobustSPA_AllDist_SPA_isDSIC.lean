-- Prove2me | Theorems.Thm_RobustSPA_AllDist_SPA_isDSIC
-- name    : RobustSPA.AllDist.SPA_isDSIC
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T08:28:23.746929+00:00
-- url     : https://prove2.me/theorems/7f9d6bf8-6226-46d2-a211-b27ec4281be0
-- title:
--   p. 16, §3.2 — for any reserve distribution Φ, SPA(Φ) ∈ 𝓜
-- statement:
--   Let $\Phi$ be any probability distribution on $\mathbb R$ and $n \ge 0$. The second-price auction with random reserve $\mathrm{SPA}(\Phi)$ for $n$ buyers belongs to the class $\mathcal M$ of DSIC mechanisms:
--   $$\mathrm{SPA}(\Phi) \in \mathcal M,$$
--   that is, on the type cube $[0,1]^n$ its allocation probabilities lie in $[0,1]$ and sum to at most $1$, every buyer weakly prefers participating to the outside option (IR), and truthful reporting is a dominant strategy (IC).
--
--   This is what makes $\mathrm{SPA}(\Phi^*)$ an admissible choice of the seller in the minimax problem, so that it bounds the minimax regret from above.
--
--   **Formalization Note** Membership in $\mathcal M$ includes the disclosed additions of the model: the allocation and payment functions are measurable and the payments are bounded on $[0,1]^n$. Ties are broken towards the lowest index.
-- source:
--   Anunrojwong, Balseiro & Besbes, On the Robustness of Second-Price Auctions in Prior-Independent Mechanism Design, arXiv:2204.10478v5, p. 16, §3.2 ("As noted earlier, for any Φ, SPA(Φ) ∈ 𝓜"); p. 13 ("It is straightforward that such mechanisms are DSIC")

import Mathlib
import Definitions.Def_RobustSPA_AllDist_Setting
open MeasureTheory

namespace RobustSPA.AllDist

/-- p. 16 (and p. 13): for any reserve law `Φ`, `SPA(Φ) ∈ 𝓜`. -/
theorem SPA_isDSIC (n : ℕ) (ρ : ProbabilityMeasure ℝ) :
    (SPA (n := n) (ρ : Measure ℝ)).IsDSIC := by sorry

end RobustSPA.AllDist
