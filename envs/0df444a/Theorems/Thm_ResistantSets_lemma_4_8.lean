-- Prove2me | Theorems.Thm_ResistantSets_lemma_4_8
-- name    : ResistantSets.lemma_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:28:19.745776+00:00
-- url     : https://prove2.me/theorems/339877db-0bb0-4add-9cf6-927d7758a3e9
-- title:
--   Lemma 4.8 (Sight Propagation) — a valid pair moves with its infeasible end
-- statement:
--   Let $n\ge1$, let $S\subseteq\{0,1\}^n$ be resistant and let $[x,y]$ be a valid pair. For a coordinate $i$ such that $x\triangle e_i$ is infeasible, exactly one of the following statements holds:
--
--   1. $y\triangle e_i$ is feasible and $[x\triangle e_i,\,y\triangle e_i]$ is valid;
--   2. $y\triangle e_i$ is infeasible and $[x\triangle e_i,\,y]$ is valid.
--
--   The lemma lets the point seen by an infeasible point be followed along infeasible paths; Path Propagation (Lemma 4.10) and most arguments of §5 rest on it.
--
--   Differences from the source:
--   - encoding: points of {0,1}ⁿ with coordinates 1, …, n → Fin n → Bool, coordinate i is the index i − 1; reason: Lean convention; same points
-- source:
--   Abdi, Cornuéjols, Lee, Resistant sets in the unit hypercube, accepted manuscript (Oct. 28, 2019), LSE Research Online 102397, Lemma 4.8 (Sight Propagation), p.17 (PDF p.18)

import Mathlib
import Definitions.Def_ResistantSets_twist
import Definitions.Def_ResistantSets_IsResistant
import Definitions.Def_ResistantSets_IsValidPair

namespace ResistantSets

/-- **Lemma 4.8 (Sight Propagation)** (Abdi, Cornuéjols, Lee, *Resistant sets in the unit hypercube*, accepted manuscript (Oct. 28, 2019), p.17): "Take an integer n ≥ 1, a resistant set
S ⊆ {0,1}ⁿ and a valid pair [x, y]. For a coordinate i ∈ [n] such that x△eᵢ is infeasible,
exactly one of the following statements holds: (i) y△eᵢ is feasible and [x△eᵢ, y△eᵢ] is valid,
(ii) y△eᵢ is infeasible and [x△eᵢ, y] is valid."

**Formalization Note** "Exactly one" is `Xor`. -/
theorem lemma_4_8 {n : ℕ} (hn : 1 ≤ n) (S : Finset (Fin n → Bool)) (hS : IsResistant S)
    (x y : Fin n → Bool) (hxy : IsValidPair S x y) (i : Fin n)
    (hi : vxor x (unitVec i) ∉ S) :
    Xor (vxor y (unitVec i) ∈ S ∧ IsValidPair S (vxor x (unitVec i)) (vxor y (unitVec i)))
      (vxor y (unitVec i) ∉ S ∧ IsValidPair S (vxor x (unitVec i)) y) := by sorry

end ResistantSets
