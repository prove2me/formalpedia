-- Prove2me | Theorems.Thm_ResistantSets_lemma_4_6
-- name    : ResistantSets.lemma_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:27:58.982021+00:00
-- url     : https://prove2.me/theorems/167efda3-dda1-450c-90e5-c5381cc31734
-- title:
--   Lemma 4.6 (Plane Propagation) — a resistant set inside $\{x_n=1\}$ is a hypercube
-- statement:
--   Let $n\ge1$ and let $S\subseteq\{0,1\}^n$ be resistant. If
--   $$
--   S\cap\{x : x_n=0\}=\emptyset,
--   $$
--   then $S$ is a hypercube (possibly empty).
--
--   This is the first of the three propagation lemmas for resistant sets; it closes the induction step of Lemma 5.4.
--
--   Differences from the source:
--   - encoding: points of {0,1}ⁿ with coordinates 1, …, n → Fin n → Bool, coordinate i is the index i − 1; reason: Lean convention; same points
--   - encoding: "a hypercube" → IsHypercube T: T = ∅ or T is a face {x : xᵢ = aᵢ, i ∈ I}; reason: the paper counts the empty set (p.29, "(possibly empty) hypercube")
-- source:
--   Abdi, Cornuéjols, Lee, Resistant sets in the unit hypercube, accepted manuscript (Oct. 28, 2019), LSE Research Online 102397, Lemma 4.6 (Plane Propagation), p.16 (PDF p.17)

import Mathlib
import Definitions.Def_ResistantSets_twist
import Definitions.Def_ResistantSets_IsResistant
import Definitions.Def_ResistantSets_IsHypercube

namespace ResistantSets

/-- **Lemma 4.6 (Plane Propagation)** (Abdi, Cornuéjols, Lee, *Resistant sets in the unit hypercube*, accepted manuscript (Oct. 28, 2019), p.16): "Take an integer n ≥ 1 and a resistant set
S ⊆ {0,1}ⁿ. If S ∩ {x : xₙ = 0} = ∅, then S is a hypercube."

**Formalization Note** Coordinate `n` is the index `n − 1` (`lastCoord`). The hypercube may be
empty (`IsHypercube`), as `S = ∅` satisfies the hypothesis. -/
theorem lemma_4_6 {n : ℕ} (hn : 1 ≤ n) (S : Finset (Fin n → Bool)) (hS : IsResistant S)
    (h0 : S.filter (fun x => x (lastCoord n (by omega)) = false) = ∅) :
    IsHypercube S := by sorry

end ResistantSets
