-- Prove2me | Theorems.Thm_PriorityAlloc_DAFlex_proposition_H_3
-- name    : PriorityAlloc.DAFlex.proposition_H_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:39:31.081989+00:00
-- url     : https://prove2.me/theorems/d0543367-6d76-43e7-b1cc-72bad3dfe124
-- title:
--   Proposition H.3, p. 48 — in a regular market, DA-STB with boosts b_tj = Σ_{S∋j} y_tS and quotas = LHS of (11) implements every nested-within-segment y ∈ Y^M
-- statement:
--   Let $M$ be a regular market satisfying the standing assumptions and let $y \in Y^M$ be nested within segment. Set the priority boosts to $b_{tj} = \sum_{S \ni j} y_{tS}$ and the quotas $q_j$ to the left-hand side of (11). Then the DA-STB mechanism with priorities $\pi_{ij} = b_{tj} + \delta_i$, $\delta_i \sim \mathrm{Uniform}(0,1)$, priority space $[0,2]^n$ and quotas $q$ implements $y$: its DA cutoff $z$ exists and
--   $$\mathbb{P}_{\delta}(B_\pi = S) = y_{tS} \qquad \text{for all } t, S.$$
--
--   This is the sufficiency half of part a-ii) of Theorem 1.
-- source:
--   Shi, Optimal Priority-Based Allocation Mechanisms, SSRN manuscript 3425348 (June 2020; published Management Science 2022, doi:10.1287/mnsc.2020.3925), p. 48, Proposition H.3

import Mathlib
import Definitions.Def_PriorityAlloc_DAFlex_Model

namespace PriorityAlloc.DAFlex

open MeasureTheory Classical

variable {m n : ℕ}

/-- Proposition H.3, p. 48: in a regular market, for `y ∈ Y^M` nested within segment, the DA-STB
mechanism with boosts `b_{tj} = Σ_{S ∋ j} y_{tS}`, priority space `[0,2]^n` and quotas `q = ` the
left-hand side of (11) implements `y`. -/
theorem proposition_H_3 (M : Market m n) (hM : M.Standing) (hreg : Regular M)
    (y : Fin m → Finset (Option (Fin n)) → ℝ) (hy : Ymem M y) (hnest : NestedWithinSegment y) :
    ∃ z, IsDACutoff M (stbLaw (stbBoost y)) (lhs11 M y) 2 z ∧
      ∀ t S, bsProb (stbLaw (stbBoost y)) z t S = y t S := by sorry

end PriorityAlloc.DAFlex
