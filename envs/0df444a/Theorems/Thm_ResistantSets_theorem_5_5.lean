-- Prove2me | Theorems.Thm_ResistantSets_theorem_5_5
-- name    : ResistantSets.theorem_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:28:32.428344+00:00
-- url     : https://prove2.me/theorems/d6c3a7ff-b769-48b2-bdeb-440ac3d6e6d0
-- title:
--   Theorem 5.5 — a lifted straight infeasible circuit of length $2(n-1)$ forces an $R_{k,1}$ ($k\le n-2$) or $R_5$ restriction
-- statement:
--   Let $n\ge4$ and let $S\subseteq\{0,1\}^n$ be a resistant, non-polar set. Assume that there is a straight infeasible circuit $K$ of length $2(n-1)$ contained in $\{x : x_n=0\}$ such that $V(K\triangle e_n)\subseteq S$. Then $S$ has one of
--   $$
--   \{R_{k,1} : 1\le k\le n-2\}\cup\{R_5\}
--   $$
--   as a restriction.
--
--   This is the main result of §5; Theorem 6.2 reduces to it.
--
--   Differences from the source:
--   - encoding: points of {0,1}ⁿ with coordinates 1, …, n → Fin n → Bool, coordinate i is the index i − 1; reason: Lean convention; same points
--   - encoding: "S has a T restriction": a series of 0/1-restrictions followed by an isomorphism (footnote 3, p.5) → HasRestriction S T: one restriction restrict S ι a fixing the coordinates outside the range of an injection ι : Fin m ↪ Fin n, with 1 ≤ m, followed by IsIso; reason: a series of 0/1-restrictions fixes a set of coordinates; ι may relabel, which IsIso allows anyway; every statement of the paper takes n ≥ 1, so 0-dimensional restrictions are never meant
--   - encoding: a straight infeasible circuit K of length 2(n − 1) contained in {x : xₙ = 0} with V(K△eₙ) ⊆ S → K = (v₀ : ι) with ι : Fin (n − 1) → Fin n and IsStraightCircuit ι; every vertex of circuitVerts v₀ ι is ∉ S, has last coordinate 0, and lifts by eₙ into S; reason: K enters the statement only through its vertex set and its length 2ℓ; same instances
-- source:
--   Abdi, Cornuéjols, Lee, Resistant sets in the unit hypercube, accepted manuscript (Oct. 28, 2019), LSE Research Online 102397, Theorem 5.5, p.35 (PDF p.36)

import Mathlib
import Definitions.Def_ResistantSets_twist
import Definitions.Def_ResistantSets_IsResistant
import Definitions.Def_ResistantSets_IsPolar
import Definitions.Def_ResistantSets_HasRestriction
import Definitions.Def_ResistantSets_Rk1
import Definitions.Def_ResistantSets_R5
import Definitions.Def_ResistantSets_circuitVerts

namespace ResistantSets

/-- **Theorem 5.5** (Abdi, Cornuéjols, Lee, *Resistant sets in the unit hypercube*, accepted manuscript (Oct. 28, 2019), p.35): "Take an integer n ≥ 4 and a resistant set S ⊆ {0,1}ⁿ that is
non-polar. Assume that there is a straight infeasible circuit K of length 2(n − 1) contained in
{x : xₙ = 0} such that V(K△eₙ) ⊆ S. Then S has one of {R_{k,1} : 1 ≤ k ≤ n − 2} ∪ {R5} as a
restriction."

**Formalization Note** `K = (v₀ : ι)` with `ι` of length `n − 1`; coordinate `n` is the index
`n − 1` (`lastCoord`). "Restriction" is isomorphic restriction (footnote 3, p.5). -/
theorem theorem_5_5 {n : ℕ} (hn : 4 ≤ n) (S : Finset (Fin n → Bool)) (hS : IsResistant S)
    (hnp : ¬ IsPolar S) (v₀ : Fin n → Bool) (ι : Fin (n - 1) → Fin n)
    (hK : IsStraightCircuit ι)
    (hKinf : ∀ w ∈ circuitVerts v₀ ι, w ∉ S)
    (hKplane : ∀ w ∈ circuitVerts v₀ ι, w (lastCoord n (by omega)) = false)
    (hKlift : ∀ w ∈ circuitVerts v₀ ι, vxor w (unitVec (lastCoord n (by omega))) ∈ S) :
    (∃ k : ℕ, 1 ≤ k ∧ k ≤ n - 2 ∧ HasRestriction S (Rk1 k)) ∨ HasRestriction S R5 := by sorry

end ResistantSets
