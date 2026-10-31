-- Prove2me | Theorems.Thm_ResistantSets_lemma_5_1
-- name    : ResistantSets.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:28:31.732761+00:00
-- url     : https://prove2.me/theorems/3772a2ed-81a3-411b-95dc-5a212f5b186d
-- title:
--   Lemma 5.1 (Straight Circuit) — neighbours of a lifted straight infeasible circuit satisfy $(\diamond)$
-- statement:
--   Let $n\ge4$ and let $S\subseteq\{0,1\}^n$ be a resistant set without antipodal points. Let $K$ be a straight infeasible circuit of length $2(n-1)$ contained in $\{x : x_n=0\}$ such that $V(K\triangle e_n)\subseteq S$. Then for every vertex $v\in\{x : x_n=0\}\setminus V(K)$ adjacent to a vertex of $K$, either
--   $$
--   \{v,\ \mathbf 1-v\triangle e_n\}\subseteq\overline S\quad\text{and}\quad\{v\triangle e_n,\ \mathbf 1-v\}\subseteq S,
--   $$
--   or
--   $$
--   \{v,\ \mathbf 1-v\triangle e_n\}\subseteq S\quad\text{and}\quad\{v\triangle e_n,\ \mathbf 1-v\}\subseteq\overline S .
--   $$
--
--   The lemma is used throughout §5: it fixes the feasibility of the points next to the circuit, which starts the inductions of Lemmas 5.2 and 5.4.
--
--   Differences from the source:
--   - encoding: points of {0,1}ⁿ with coordinates 1, …, n → Fin n → Bool, coordinate i is the index i − 1; reason: Lean convention; same points
--   - encoding: a straight infeasible circuit K of length 2(n − 1) contained in {x : xₙ = 0} with V(K△eₙ) ⊆ S → K = (v₀ : ι) with ι : Fin (n − 1) → Fin n and IsStraightCircuit ι; every vertex of circuitVerts v₀ ι is ∉ S, has last coordinate 0, and lifts by eₙ into S; reason: K enters the statement only through its vertex set and its length 2ℓ; same instances
-- source:
--   Abdi, Cornuéjols, Lee, Resistant sets in the unit hypercube, accepted manuscript (Oct. 28, 2019), LSE Research Online 102397, Lemma 5.1 (Straight Circuit), p.23 (PDF p.24)

import Mathlib
import Definitions.Def_ResistantSets_twist
import Definitions.Def_ResistantSets_IsResistant
import Definitions.Def_ResistantSets_IsPolar
import Definitions.Def_ResistantSets_circuitVerts

namespace ResistantSets

/-- **Lemma 5.1 (Straight Circuit)** (Abdi, Cornuéjols, Lee, *Resistant sets in the unit hypercube*, accepted manuscript (Oct. 28, 2019), p.23): "Take an integer n ≥ 4 and a resistant set
S ⊆ {0,1}ⁿ without antipodal points. Let K be a straight infeasible circuit of length 2(n − 1)
contained in {x : xₙ = 0} such that V(K△eₙ) ⊆ S. Then for a vertex v ∈ {x : xₙ = 0} − V(K) that
is adjacent to a vertex of K, either {v, 1 − v△eₙ} ⊆ S̄ and {v△eₙ, 1 − v} ⊆ S or
{v, 1 − v△eₙ} ⊆ S and {v△eₙ, 1 − v} ⊆ S̄."

The circuit is `K = (v₀ : i₁, …, i_{n−1})` with coordinate sequence `ι` of length `n − 1` (so
`K` has length `2(n − 1)`); the vertex called `v` on the page is `u` here.

**Formalization Note** Coordinate `n` is the index `n − 1` (`lastCoord`); `1 − w` is
`cmpl w`. "Adjacent" in `Gₙ` means differing in exactly one coordinate. -/
theorem lemma_5_1 {n : ℕ} (hn : 4 ≤ n) (S : Finset (Fin n → Bool)) (hS : IsResistant S)
    (hanti : ¬ HasAntipodal S) (v₀ : Fin n → Bool) (ι : Fin (n - 1) → Fin n)
    (hK : IsStraightCircuit ι)
    (hKinf : ∀ w ∈ circuitVerts v₀ ι, w ∉ S)
    (hKplane : ∀ w ∈ circuitVerts v₀ ι, w (lastCoord n (by omega)) = false)
    (hKlift : ∀ w ∈ circuitVerts v₀ ι, vxor w (unitVec (lastCoord n (by omega))) ∈ S)
    (u : Fin n → Bool) (hu : u (lastCoord n (by omega)) = false) (huK : u ∉ circuitVerts v₀ ι)
    (hadj : ∃ w ∈ circuitVerts v₀ ι, ∃ i : Fin n, u = vxor w (unitVec i)) :
    (u ∉ S ∧ cmpl (vxor u (unitVec (lastCoord n (by omega)))) ∉ S ∧
        vxor u (unitVec (lastCoord n (by omega))) ∈ S ∧ cmpl u ∈ S) ∨
      (u ∈ S ∧ cmpl (vxor u (unitVec (lastCoord n (by omega)))) ∈ S ∧
        vxor u (unitVec (lastCoord n (by omega))) ∉ S ∧ cmpl u ∉ S) := by sorry

end ResistantSets
