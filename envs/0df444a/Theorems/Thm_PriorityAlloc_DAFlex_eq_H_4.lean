-- Prove2me | Theorems.Thm_PriorityAlloc_DAFlex_eq_H_4
-- name    : PriorityAlloc.DAFlex.eq_H_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:39:09.226969+00:00
-- url     : https://prove2.me/theorems/3f0acbc5-f5e0-4cc3-a773-2be5d2ef5b1f
-- title:
--   (H.4), proof of Proposition H.1, p. 47 — in a regular market, a cutoff z′ ≤ 𝟏 that changes the budget set probabilities assigns strictly less mass to the outside option
-- statement:
--   Let $M$ be a regular market satisfying the standing assumptions, $y \in Y^M$, $G_t$ the priority law (H.1) and $q_j$ the left-hand side of (11). Let $z' \in [0,2]^n$ with $z' \le \mathbf 1$ componentwise, and suppose the budget set probabilities under $z'$ differ from $y$: $\mathbb{P}_{\pi \sim G_t}(B'_\pi = S) \ne y_{tS}$ for some $t$ and $S$, where $B'_\pi = \{j : j = 0 \text{ or } \pi_j \ge z'_j\}$. Then, with $\Lambda = \sum_t \lambda_t$,
--   $$\Lambda - \sum_{j \in [n]} D_j(z') \;<\; \Lambda - \sum_{j \in [n]} q_j .$$
--
--   The two sides are the masses assigned to the outside option under the cutoffs $z'$ and $\mathbf 1$. This strict inequality is where regularity enters the proof that DA implements every feasible $y$.
-- source:
--   Shi, Optimal Priority-Based Allocation Mechanisms, SSRN manuscript 3425348 (June 2020; published Management Science 2022, doi:10.1287/mnsc.2020.3925), p. 47, proof of Proposition H.1, eq. (H.4)

import Mathlib
import Definitions.Def_PriorityAlloc_DAFlex_Model

namespace PriorityAlloc.DAFlex

open MeasureTheory Classical

variable {m n : ℕ}

/-- (H.4), proof of Proposition H.1, p. 47: in a regular market, if a cutoff vector
`z' ≤ 𝟏` in `[0,2]^n` yields budget set probabilities different from `y` under the priority law
(H.1), then strictly less mass is assigned to the outside option than under `y`:
`Λ − Σ_j D_j(z') < Λ − Σ_j q_j` with `Λ = Σ_t λ_t` and `q` the left-hand side of (11). -/
theorem eq_H_4 (M : Market m n) (hM : M.Standing) (hreg : Regular M)
    (y : Fin m → Finset (Option (Fin n)) → ℝ) (hy : Ymem M y) (z : Fin n → ℝ)
    (hzbox : z ∈ box 2) (hz1 : z ≤ 1)
    (hne : ∃ t S, bsProb (h1Law y) z t S ≠ y t S) :
    (∑ t, M.lam t) - ∑ j, demand M (h1Law y) z j < (∑ t, M.lam t) - ∑ j, lhs11 M y j := by sorry

end PriorityAlloc.DAFlex
