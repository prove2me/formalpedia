-- Prove2me | Theorems.Thm_PriorityAlloc_DAFlex_proposition_H_1
-- name    : PriorityAlloc.DAFlex.proposition_H_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:39:18.516123+00:00
-- url     : https://prove2.me/theorems/e896dda1-843f-4043-ac27-1f02c60ed31e
-- title:
--   Proposition H.1, p. 47 — in a regular market, DA with priorities (H.1) on [0,2]^n and quotas = LHS of (11) implements every y ∈ Y^M
-- statement:
--   Let $M$ be a regular market satisfying the standing assumptions and $y \in Y^M$. Define the priority distribution $G_t$ of segment $t$ by sampling $S_i \subseteq J$ with probability $y_{tS_i}$ and setting
--   $$\pi_{ij} = \mathbb{1}(j \in S_i) + \delta_i, \qquad \delta_i \sim \mathrm{Uniform}(0,1), \tag{H.1}$$
--   and let the quota $q_j$ be the left-hand side of (11). Then the DA mechanism with priority distributions $G$, priority space $[0,2]^n$ and quota vector $q$ implements $y$: its DA cutoff $z$ exists and
--   $$\mathbb{P}_{\pi \sim G_t}(B_\pi = S) = y_{tS} \qquad \text{for all } t, S.$$
--
--   This is the flexibility of DA: in a regular market, optimizing over DA priorities and quotas is as good as optimizing over all priority-based mechanisms. It gives part a-i) of Theorem 1.
-- source:
--   Shi, Optimal Priority-Based Allocation Mechanisms, SSRN manuscript 3425348 (June 2020; published Management Science 2022, doi:10.1287/mnsc.2020.3925), p. 47, Proposition H.1

import Mathlib
import Definitions.Def_PriorityAlloc_DAFlex_Model

namespace PriorityAlloc.DAFlex

open MeasureTheory Classical

variable {m n : ℕ}

/-- Proposition H.1, p. 47 (flexibility of DA): in a regular market, for `y ∈ Y^M`, the DA
mechanism with priority distributions (H.1), priority space `[0,2]^n` and quotas `q = ` the
left-hand side of (11) implements `y`. -/
theorem proposition_H_1 (M : Market m n) (hM : M.Standing) (hreg : Regular M)
    (y : Fin m → Finset (Option (Fin n)) → ℝ) (hy : Ymem M y) :
    ∃ z, IsDACutoff M (h1Law y) (lhs11 M y) 2 z ∧ ∀ t S, bsProb (h1Law y) z t S = y t S := by sorry

end PriorityAlloc.DAFlex
