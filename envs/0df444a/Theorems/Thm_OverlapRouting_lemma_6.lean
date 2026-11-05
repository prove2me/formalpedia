-- Prove2me | Theorems.Thm_OverlapRouting_lemma_6
-- name    : OverlapRouting.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:37:26.604981+00:00
-- url     : https://prove2.me/theorems/6c5e901d-20d9-417b-ba28-780148423c52
-- title:
--   Lemma 6 — $\mathbb E[R_j]\le\mathbb E[R_1]$
-- statement:
--   Let $N'\ge1$, $Q\ge1$ and $D$ any demand law. For every $M$ and every $1\le j\le M$,
--   $$\mathbb E[R_j]\ \le\ \mathbb E[R_1].$$
--
--   Hence $r_{avg}\le\mathbb E[R_1]$, a bound independent of $M$ used to control the error terms in Theorem 1.
--
--   Differences from the source:
--   - reading: "D can only take non-negative integer values and has finite support {0} ∪ [u]" (p.5) → any probability mass function p on {0,…,u} (values may have mass 0); reason: the authors' own usage in Appendix A, p.34 (WLOG aperiodic, P[D̄ > Q] > 0); the more general reading, which contains the literal one
--   - encoding: E[Rⱼ], the expected number of trips of vehicle j → expTrips: the expectation of rⱼ = ⌈wⱼ/Q⌉ from the recursion (3), over i.i.d. demands; reason: (3) is the paper's own definition of the trip count; Eq. (3) milestone ties it to the driven routes
-- source:
--   Ledvina, Qin, Simchi-Levi & Wei, A New Approach for Vehicle Routing with Stochastic Demand: Combining Route Assignment with Process Flexibility, SSRN 3656374 (PDF of 2022-03-11), https://ssrn.com/abstract=3656374, Lemma 6, p.17

import Mathlib
import Definitions.Def_OverlapRouting_vrpOpt
import Definitions.Def_OverlapRouting_DemandLaw
import Definitions.Def_OverlapRouting_costAO
import Definitions.Def_OverlapRouting_ZAO

namespace OverlapRouting

/-- **Lemma 6**, p.17 (Ledvina, Qin, Simchi-Levi & Wei, SSRN 3656374 (2022)): "For a fixed `M` and
any `1 ≤ j ≤ M`, we have that `E[Rⱼ] ≤ E[R₁]`." -/
theorem lemma_6 (N' Q : ℕ) (hN' : 1 ≤ N') (hQ : 1 ≤ Q) (D : DemandLaw) (M j : ℕ) (hj : 1 ≤ j)
    (hjM : j ≤ M) :
    expTrips N' Q D M j ≤ expTrips N' Q D M 1 := by sorry

end OverlapRouting
