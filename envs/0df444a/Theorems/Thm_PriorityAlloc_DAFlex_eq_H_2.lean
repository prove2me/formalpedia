-- Prove2me | Theorems.Thm_PriorityAlloc_DAFlex_eq_H_2
-- name    : PriorityAlloc.DAFlex.eq_H_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:39:08.360096+00:00
-- url     : https://prove2.me/theorems/4ca9a775-8505-4c22-ab79-dcd1491f4ab4
-- title:
--   (H.2), proof of Proposition H.1, p. 47 — under the priorities (H.1) the all-ones cutoff gives D_j(𝟏) = q_j and is a fixed point of the DA operator
-- statement:
--   Let $M$ satisfy the standing assumptions and let $y \in Y^M$. Give segment $t$ the priority law (H.1): draw $S \subseteq J$ with probability $y_{tS}$ and $\delta \sim \mathrm{Uniform}(0,1)$, and set $\pi_j = \mathbb{1}(j \in S) + \delta$. Let the quota be $q_j = \sum_{t,S} \lambda_t P_t(j,S)\, y_{tS}$, the left-hand side of (11). Then, with $\mathbf 1$ the all-ones cutoff vector,
--   $$D_j(\mathbf 1) = \sum_{t \in [m]} \sum_{S} \lambda_t P_t(j,S)\, y_{tS} = q_j \qquad \text{for every } j \in [n],$$
--   and $\mathbf 1$ is a fixed point of the DA operator on $\Pi = [0,2]^n$: $DA(\mathbf 1) = \mathbf 1$.
--
--   This is the first step of the proof that DA can implement every feasible budget set probability matrix.
--
--   **Formalization Note** The printed (H.2) omits the sum over $S$; the quota is by construction the full left-hand side of (11), which is what the Lean states.
-- source:
--   Shi, Optimal Priority-Based Allocation Mechanisms, SSRN manuscript 3425348 (June 2020; published Management Science 2022, doi:10.1287/mnsc.2020.3925), p. 47, proof of Proposition H.1, eq. (H.2)

import Mathlib
import Definitions.Def_PriorityAlloc_DAFlex_Model

namespace PriorityAlloc.DAFlex

open MeasureTheory Classical

variable {m n : ℕ}

/-- (H.2), proof of Proposition H.1, p. 47: under the priority law (H.1) and quotas
`q = ` the left-hand side of (11), the all-ones cutoff vector gives `D_j(𝟏) = q_j` for every item,
so `𝟏` is a fixed point of the DA operator on `Π = [0,2]^n`. -/
theorem eq_H_2 (M : Market m n) (hM : M.Standing) (y : Fin m → Finset (Option (Fin n)) → ℝ)
    (hy : Ymem M y) :
    (∀ j, demand M (h1Law y) 1 j = lhs11 M y j) ∧
      DAop M (h1Law y) (lhs11 M y) 2 1 = 1 := by sorry

end PriorityAlloc.DAFlex
