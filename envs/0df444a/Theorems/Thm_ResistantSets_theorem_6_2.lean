-- Prove2me | Theorems.Thm_ResistantSets_theorem_6_2
-- name    : ResistantSets.theorem_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:28:26.803478+00:00
-- url     : https://prove2.me/theorems/42afe9b9-abed-4272-aac5-244f2be81eb9
-- title:
--   Theorem 6.2 — resistant non-polar sets with straight infeasible paths of length $\le n-1$ have an $R_{k,1}$ or $R_5$ restriction
-- statement:
--   Let $n\ge3$ and let $S\subseteq\{0,1\}^n$ be a resistant, non-polar set. If every straight infeasible path has length at most $n-1$, then $S$ has one of
--   $$
--   \{R_{k,1} : k\ge1\}\cup\{R_5\}
--   $$
--   as a restriction.
--
--   For a half-dense non-polar set exactly one of $x$ and $\mathbf 1-x$ is feasible, so the path hypothesis holds; this is how Theorem 1.17 follows.
--
--   Differences from the source:
--   - encoding: points of {0,1}ⁿ with coordinates 1, …, n → Fin n → Bool, coordinate i is the index i − 1; reason: Lean convention; same points
--   - encoding: "S has a T restriction": a series of 0/1-restrictions followed by an isomorphism (footnote 3, p.5) → HasRestriction S T: one restriction restrict S ι a fixing the coordinates outside the range of an injection ι : Fin m ↪ Fin n, with 1 ≤ m, followed by IsIso; reason: a series of 0/1-restrictions fixes a set of coordinates; ι may relabel, which IsIso allows anyway; every statement of the paper takes n ≥ 1, so 0-dimensional restrictions are never meant
--   - encoding: straight infeasible path: a path of Gₙ[S̄] of length dist(a, b) → IsStraightInfeasiblePath S a ι: start a and distinct flipped coordinates ι : Fin ℓ → Fin n, every vertex infeasible; reason: Remark 4.2 (p.15): the straight paths are exactly these
-- source:
--   Abdi, Cornuéjols, Lee, Resistant sets in the unit hypercube, accepted manuscript (Oct. 28, 2019), LSE Research Online 102397, Theorem 6.2, p.36 (PDF p.37)

import Mathlib
import Definitions.Def_ResistantSets_IsResistant
import Definitions.Def_ResistantSets_IsPolar
import Definitions.Def_ResistantSets_HasRestriction
import Definitions.Def_ResistantSets_Rk1
import Definitions.Def_ResistantSets_R5
import Definitions.Def_ResistantSets_IsStraightInfeasiblePath

namespace ResistantSets

/-- **Theorem 6.2** (Abdi, Cornuéjols, Lee, *Resistant sets in the unit hypercube*, accepted manuscript (Oct. 28, 2019), p.36): "Take an integer n ≥ 3 and a resistant set S ⊆ {0,1}ⁿ that is
non-polar. If every straight infeasible path has length at most n − 1, then S has one of
{R_{k,1} : k ≥ 1} ∪ {R5} as a restriction."

**Formalization Note** Straight infeasible paths as in `IsStraightInfeasiblePath` (Remark 4.2).
"Restriction" is isomorphic restriction (footnote 3, p.5). -/
theorem theorem_6_2 {n : ℕ} (hn : 3 ≤ n) (S : Finset (Fin n → Bool)) (hS : IsResistant S)
    (hnp : ¬ IsPolar S)
    (hpath : ∀ (ℓ : ℕ) (a : Fin n → Bool) (ι : Fin ℓ → Fin n),
      IsStraightInfeasiblePath S a ι → ℓ ≤ n - 1) :
    (∃ k : ℕ, 1 ≤ k ∧ HasRestriction S (Rk1 k)) ∨ HasRestriction S R5 := by sorry

end ResistantSets
