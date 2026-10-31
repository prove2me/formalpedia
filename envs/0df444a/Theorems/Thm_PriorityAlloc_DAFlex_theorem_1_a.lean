-- Prove2me | Theorems.Thm_PriorityAlloc_DAFlex_theorem_1_a
-- name    : PriorityAlloc.DAFlex.theorem_1_a
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:39:18.218944+00:00
-- url     : https://prove2.me/theorems/3f08b2f6-a5e2-4a86-ba95-cd803350c483
-- title:
--   Theorem 1 a), p. 13 — in a regular market, DA implements every y ∈ Y^M, and DA-STB implements y iff y is nested within segment
-- statement:
--   Let $M = (m, n, \lambda, c, F)$ be a market satisfying the standing assumptions of §2 and let $Y^M$ be its set of feasible budget set probabilities (Definition 2). If $M$ is regular (Definition 4), then
--
--   1. every $y \in Y^M$ is implementable using the class of deferred acceptance (DA) mechanisms;
--   2. a matrix $y \in Y^M$ is implementable using the class of DA-STB mechanisms if and only if $y$ is nested within segment.
--
--   $$M \text{ regular} \;\Longrightarrow\; Y^M \subseteq \{\text{DA-implementable}\}, \qquad \{\text{DA-STB-implementable}\} \cap Y^M = \{y \in Y^M : y \text{ nested within segment}\}.$$
--
--   Part i) says that, in regular markets, optimizing priority distributions and quotas under DA loses nothing relative to optimizing over all priority-based allocation mechanisms; the planner's design problem reduces to a linear program over $Y^M$. Part ii) identifies exactly what single tie-breaking costs.
--
--   **Formalization Note** Implementability quantifies over mechanism parameters (a priority box $[0,B]^n$, priority laws on it, quotas $0 \le q \le c$, and the DA cutoff as the least fixed point of the DA operator), never over budget sets directly. Part b) of Theorem 1 (TTC and serial dictatorship) is not part of this statement.
-- source:
--   Shi, Optimal Priority-Based Allocation Mechanisms, SSRN manuscript 3425348 (June 2020; published Management Science 2022, doi:10.1287/mnsc.2020.3925), p. 13, Theorem 1 a) (parts a-i and a-ii)

import Mathlib
import Definitions.Def_PriorityAlloc_DAFlex_Model

namespace PriorityAlloc.DAFlex

open MeasureTheory Classical

variable {m n : ℕ}

/-- Theorem 1 a), p. 13: in a regular market, (i) every `y ∈ Y^M` is implementable by a DA
mechanism, and (ii) `y ∈ Y^M` is implementable by a DA-STB mechanism iff it is nested within
segment. -/
theorem theorem_1_a (M : Market m n) (hM : M.Standing) (hreg : Regular M) :
    (∀ y, Ymem M y → DAImplementable M y) ∧
      (∀ y, Ymem M y → (DASTBImplementable M y ↔ NestedWithinSegment y)) := by sorry

end PriorityAlloc.DAFlex
