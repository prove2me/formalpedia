-- Prove2me | Theorems.Thm_PriorityAlloc_DAFlex_proposition_H_2_a
-- name    : PriorityAlloc.DAFlex.proposition_H_2_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:39:20.650874+00:00
-- url     : https://prove2.me/theorems/46c0311f-0981-4295-919f-1d4f553d16d8
-- title:
--   Proposition H.2 a), p. 48 — the budget set probabilities arising from DA-STB are always nested within segment
-- statement:
--   Let $b$ be any $m \times n$ matrix of priority boosts and give segment $t$ the DA-STB priorities $\pi_{ij} = b_{tj} + \delta_i$ with a single tie-breaker $\delta_i \sim \mathrm{Uniform}(0,1)$. For every cutoff vector $z$, the budget set probabilities
--   $$y_{tS} = \mathbb{P}_{\delta}\big(\{j \in J : j = 0 \text{ or } b_{tj} + \delta \ge z_j\} = S\big)$$
--   are nested within segment: if $y_{tS} > 0$ and $y_{tS'} > 0$, then $S \subseteq S'$ or $S' \subseteq S$.
--
--   This is the necessity half of part a-ii) of Theorem 1: DA-STB can only implement nested-within-segment matrices.
--
--   **Formalization Note** The statement is proved for every cutoff vector $z$, as in the paper's proof; the DA cutoff of a DA-STB mechanism is a special case, so this is (weakly) stronger than the printed proposition.
-- source:
--   Shi, Optimal Priority-Based Allocation Mechanisms, SSRN manuscript 3425348 (June 2020; published Management Science 2022, doi:10.1287/mnsc.2020.3925), p. 48, Proposition H.2 a) and its proof

import Mathlib
import Definitions.Def_PriorityAlloc_DAFlex_Model

namespace PriorityAlloc.DAFlex

open MeasureTheory Classical

variable {m n : ℕ}

/-- Proposition H.2 a), p. 48: the budget set probabilities arising from DA-STB are always nested
within segment. Stated for every cutoff vector `z` (in particular the DA cutoff), as in its
proof. -/
theorem proposition_H_2_a (b : Fin m → Fin n → ℝ) (z : Fin n → ℝ) :
    NestedWithinSegment (bsProb (stbLaw b) z) := by sorry

end PriorityAlloc.DAFlex
