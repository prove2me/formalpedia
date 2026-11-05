-- Prove2me | Theorems.Thm_OverlapRouting_lemma_7
-- name    : OverlapRouting.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:36:44.757779+00:00
-- url     : https://prove2.me/theorems/9c4b2fb5-43ab-40ea-bb4d-2a5e836ce0b0
-- title:
--   Lemma 7 — $\mathbb E[R_j]=s^0P^{j-1}\pi$ (corrected: exponent $j-1$, not $j$)
-- statement:
--   Let $N'\ge1$, $Q\ge1$, $D$ any demand law, and let $p_d$, $P$, $\pi$, $s^0$ be the objects of Lemma 7 for $\bar D$, the sum of $N'$ i.i.d. copies of $D$. Then for every $M$ and every $1\le j\le M$,
--   $$\mathbb E[R_j]=s^0P^{\,j-1}\pi .$$
--
--   It reduces the expected trip counts to powers of a fixed finite stochastic matrix, the input to Lemma 4.
--
--   Differences from the source:
--   - correction: E[Rⱼ] = s⁰Pʲπ → E[Rⱼ] = s⁰P^{j−1}π; reason: as printed it is false: N′ = 1, Q = 2, D uniform on {0,1,2} gives E[R₁] = E⌈D/2⌉ = 2/3 but s⁰Pπ = 5/9 (proved in a verification file); the proof of Lemma 4 on p.35 uses s⁰P^{j−1}π
--   - reading: "D can only take non-negative integer values and has finite support {0} ∪ [u]" (p.5) → any probability mass function p on {0,…,u} (values may have mass 0); reason: the authors' own usage in Appendix A, p.34 (WLOG aperiodic, P[D̄ > Q] > 0); the more general reading, which contains the literal one
--   - encoding: P, π indexed by 0 ∪ [Q]; U the maximum value of D̄ → Fin (Q+1) indices; U = N′u; reason: same matrices; values of D̄ above N′u have mass 0
--   - encoding: E[Rⱼ], the expected number of trips of vehicle j → expTrips: the expectation of rⱼ = ⌈wⱼ/Q⌉ from the recursion (3), over i.i.d. demands; reason: (3) is the paper's own definition of the trip count; Eq. (3) milestone ties it to the driven routes
-- source:
--   Ledvina, Qin, Simchi-Levi & Wei, A New Approach for Vehicle Routing with Stochastic Demand: Combining Route Assignment with Process Flexibility, SSRN 3656374 (PDF of 2022-03-11), https://ssrn.com/abstract=3656374, Lemma 7, Appendix A, p.34 (proof pp.34–35)

import Mathlib
import Definitions.Def_OverlapRouting_DemandLaw
import Definitions.Def_OverlapRouting_costAO
import Definitions.Def_OverlapRouting_ZAO
import Definitions.Def_OverlapRouting_tripMatrix

open Matrix

namespace OverlapRouting

/-- **Lemma 7**, p.34 (Ledvina, Qin, Simchi-Levi & Wei, SSRN 3656374 (2022)), with the exponent
corrected from `j` to `j − 1`: for every `1 ≤ j ≤ M`,
`E[Rⱼ] = s⁰ P^{j−1} π`,
where `s⁰ = [1, 0, …, 0]`, `P` is the `(Q+1) × (Q+1)` transition matrix of the excess capacity and
`π_m = ∑_d p_d ⌈(d − m)⁺/Q⌉`, with `p_d` the pmf of the total demand `D̄` of a primary route.

**Formalization Note.** As printed (`s⁰Pʲπ`) the lemma is false: for `N′ = 1`, `Q = 2` and `D`
uniform on `{0, 1, 2}`, `E[R₁] = 2/3` but `s⁰Pπ = 5/9`. The proof on p.35 and the proof of
Lemma 4 use `s⁰P^{j−1}π`. -/
theorem lemma_7 (N' Q : ℕ) (hN' : 1 ≤ N') (hQ : 1 ≤ Q) (D : DemandLaw) (M j : ℕ) (hj : 1 ≤ j)
    (hjM : j ≤ M) :
    expTrips N' Q D M j =
      (startVector Q ᵥ* (tripMatrix N' Q D ^ (j - 1))) ⬝ᵥ tripReward N' Q D := by sorry

end OverlapRouting
