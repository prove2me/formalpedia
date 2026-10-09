-- Prove2me | Theorems.Thm_SAGFiniteSum_Rate_lyapunov_dominates
-- name    : SAGFiniteSum.Rate.lyapunov_dominates
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:18:34.847095+00:00
-- url     : https://prove2.me/theorems/29255935-5444-4bdb-9099-005d8e6443db
-- title:
--   App. B.7, p. 46 — g(xᵏ) − g(x*) ≤ ℒ(θᵏ) for the B.5 constants
-- statement:
--   Assume the standing assumptions of §3 with $n\ge2$, and let $\mathcal L$ be the Lyapunov function of App. B.2 with the constants of App. B.5. Then for every state $\theta=(y,x)$,
--   $$
--   g(x)-g(x^*)\ \le\ \mathcal L(\theta).
--   $$
--
--   This transfers bounds on $\mathbb E\,\mathcal L(\theta^k)$ to the suboptimality $\mathbb E\,g(x^k)-g(x^*)$.
--
--   **Formalization Note** Convexity of each $f_i$ suffices; no strong convexity is assumed ($\mu=0$). The parametric chain of App. B.4 (p. 42) that the page offers for this claim bounds $\|2dg'(x)+2b(x-x^*)\|$ by $2(dL+b)\|x-x^*\|$, which fails for $b<0$ (and B.5 has $b<0$); only the claim for the B.5 constants is stated, and it holds.
-- source:
--   Schmidt, Le Roux & Bach, arXiv:1309.2388v2, App. B.7, first display, p. 46 (constants of App. B.5, p. 43)

import Mathlib
import Definitions.Def_SAGFiniteSum_Rate_Model
import Definitions.Def_SAGFiniteSum_Rate_Lyapunov

open scoped RealInnerProductSpace

namespace SAGFiniteSum.Rate

/-- B.7, first display (arXiv:1309.2388v2, p. 46). With the B.5 constants and `n ≥ 2`, the
Lyapunov function dominates the suboptimality: `g(x) − g(x*) ≤ ℒ(θ)` for every state
`θ = (y, x)`. -/
theorem lyapunov_dominates {p n : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (L : ℝ)
    (xstar : EuclideanSpace ℝ (Fin p)) (hA : SAGAssumptions f f' L xstar) (hn : 2 ≤ n)
    (θ : (Fin n → EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin p)) :
    SAGA.Convex.fAvg f θ.2 - SAGA.Convex.fAvg f xstar ≤ sagLyap f f' L xstar θ := by sorry

end SAGFiniteSum.Rate
