-- Prove2me | Theorems.Thm_ResistantSets_lemma_4_10
-- name    : ResistantSets.lemma_4_10
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:28:12.922994+00:00
-- url     : https://prove2.me/theorems/abf8baf6-1a1b-44bf-a67d-4b57c04ace53
-- title:
--   Lemma 4.10 (Path Propagation) — feasible lifts of the ends of a straight infeasible path propagate
-- statement:
--   Let $n\ge1$, let $S\subseteq\{0,1\}^n$ be resistant and let $P$ be a straight infeasible path contained in the hyperplane $\{x : x_n=0\}$, with ends $a$ and $b$. If $a\triangle e_n$ and $b\triangle e_n$ are feasible, then
--   $$
--   v\triangle e_n\ \text{is feasible for every vertex } v \text{ of } P.
--   $$
--
--   Path Propagation turns information at the two ends of an infeasible path into information along the whole path; it produces the circuits of Theorem 6.2 and Lemma 5.1.
--
--   Differences from the source:
--   - encoding: points of {0,1}ⁿ with coordinates 1, …, n → Fin n → Bool, coordinate i is the index i − 1; reason: Lean convention; same points
--   - encoding: straight infeasible path: a path of Gₙ[S̄] of length dist(a, b) → IsStraightInfeasiblePath S a ι: start a and distinct flipped coordinates ι : Fin ℓ → Fin n, every vertex infeasible; reason: Remark 4.2 (p.15): the straight paths are exactly these
-- source:
--   Abdi, Cornuéjols, Lee, Resistant sets in the unit hypercube, accepted manuscript (Oct. 28, 2019), LSE Research Online 102397, Lemma 4.10 (Path Propagation), p.18 (PDF p.19)

import Mathlib
import Definitions.Def_ResistantSets_twist
import Definitions.Def_ResistantSets_IsResistant
import Definitions.Def_ResistantSets_IsStraightInfeasiblePath

namespace ResistantSets

/-- **Lemma 4.10 (Path Propagation)** (Abdi, Cornuéjols, Lee, *Resistant sets in the unit hypercube*, accepted manuscript (Oct. 28, 2019), p.18): "Take an integer n ≥ 1, a resistant set
S ⊆ {0,1}ⁿ, a straight infeasible path P contained in {x : xₙ = 0}, and let a, b be the ends of
P. If a△eₙ, b△eₙ are feasible, then for every vertex v of P, v△eₙ is feasible."

The path `P` starts at `a`, flips the distinct coordinates `ι = (i₁, …, i_ℓ)` in order, and
ends at `b = pathVertex a ι ℓ`; its vertices are `pathVertex a ι j`, `0 ≤ j ≤ ℓ`.

**Formalization Note** Coordinate `n` is the index `n − 1` (`lastCoord`). -/
theorem lemma_4_10 {n ℓ : ℕ} (hn : 1 ≤ n) (S : Finset (Fin n → Bool)) (hS : IsResistant S)
    (a : Fin n → Bool) (ι : Fin ℓ → Fin n) (hP : IsStraightInfeasiblePath S a ι)
    (hplane : ∀ j ≤ ℓ, pathVertex a ι j (lastCoord n (by omega)) = false)
    (ha : vxor a (unitVec (lastCoord n (by omega))) ∈ S)
    (hb : vxor (pathVertex a ι ℓ) (unitVec (lastCoord n (by omega))) ∈ S) :
    ∀ j ≤ ℓ, vxor (pathVertex a ι j) (unitVec (lastCoord n (by omega))) ∈ S := by sorry

end ResistantSets
