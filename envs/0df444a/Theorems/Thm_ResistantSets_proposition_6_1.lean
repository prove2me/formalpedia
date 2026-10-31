-- Prove2me | Theorems.Thm_ResistantSets_proposition_6_1
-- name    : ResistantSets.proposition_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:28:12.595781+00:00
-- url     : https://prove2.me/theorems/b4d6a2d3-621b-447e-9366-2d4a09309776
-- title:
--   Proposition 6.1 — short straight infeasible paths force an $R_{1,1}$ restriction
-- statement:
--   Let $n\ge3$ and let $S\subseteq\{0,1\}^n$ be a resistant set without antipodal points. If every straight infeasible path has length at most $n-2$, then $S$ has an $R_{1,1}$ restriction.
--
--   This settles the case of Theorem 6.2 in which no straight infeasible path has length $n-1$.
--
--   Differences from the source:
--   - encoding: points of {0,1}ⁿ with coordinates 1, …, n → Fin n → Bool, coordinate i is the index i − 1; reason: Lean convention; same points
--   - encoding: "S has a T restriction": a series of 0/1-restrictions followed by an isomorphism (footnote 3, p.5) → HasRestriction S T: one restriction restrict S ι a fixing the coordinates outside the range of an injection ι : Fin m ↪ Fin n, with 1 ≤ m, followed by IsIso; reason: a series of 0/1-restrictions fixes a set of coordinates; ι may relabel, which IsIso allows anyway; every statement of the paper takes n ≥ 1, so 0-dimensional restrictions are never meant
--   - encoding: straight infeasible path: a path of Gₙ[S̄] of length dist(a, b) → IsStraightInfeasiblePath S a ι: start a and distinct flipped coordinates ι : Fin ℓ → Fin n, every vertex infeasible; reason: Remark 4.2 (p.15): the straight paths are exactly these
-- source:
--   Abdi, Cornuéjols, Lee, Resistant sets in the unit hypercube, accepted manuscript (Oct. 28, 2019), LSE Research Online 102397, Proposition 6.1, p.35 (PDF p.36)

import Mathlib
import Definitions.Def_ResistantSets_IsResistant
import Definitions.Def_ResistantSets_IsPolar
import Definitions.Def_ResistantSets_HasRestriction
import Definitions.Def_ResistantSets_Rk1
import Definitions.Def_ResistantSets_IsStraightInfeasiblePath

namespace ResistantSets

/-- **Proposition 6.1** (Abdi, Cornuéjols, Lee, *Resistant sets in the unit hypercube*, accepted manuscript (Oct. 28, 2019), p.35): "Take an integer n ≥ 3 and a resistant set S ⊆ {0,1}ⁿ
without antipodal points. If every straight infeasible path has length at most n − 2, then S has
an R1,1 restriction."

**Formalization Note** A straight infeasible path of length `ℓ` is given by its start `a` and
its distinct flipped coordinates `ι : Fin ℓ → Fin n` (`IsStraightInfeasiblePath`, Remark 4.2).
`n − 2` is natural-number subtraction with `n ≥ 3`. -/
theorem proposition_6_1 {n : ℕ} (hn : 3 ≤ n) (S : Finset (Fin n → Bool)) (hS : IsResistant S)
    (hanti : ¬ HasAntipodal S)
    (hpath : ∀ (ℓ : ℕ) (a : Fin n → Bool) (ι : Fin ℓ → Fin n),
      IsStraightInfeasiblePath S a ι → ℓ ≤ n - 2) :
    HasRestriction S (Rk1 1) := by sorry

end ResistantSets
