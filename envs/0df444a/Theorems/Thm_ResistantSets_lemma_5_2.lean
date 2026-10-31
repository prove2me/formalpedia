-- Prove2me | Theorems.Thm_ResistantSets_lemma_5_2
-- name    : ResistantSets.lemma_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:28:38.091984+00:00
-- url     : https://prove2.me/theorems/f02b6ecb-c1a9-42e3-b51a-532104179ee3
-- title:
--   Lemma 5.2 — rerouting the circuit $(\mathbf 0:1,\dots,n-1)$
-- statement:
--   Let $n\ge6$ and let $S\subseteq\{0,1\}^n$ be a resistant set without antipodal points and without an $R_{1,1}$ or $R_5$ restriction. Suppose that $K=(\mathbf 0:1,2,\dots,n-1)$ is a straight infeasible circuit, $V(K\triangle e_n)\subseteq S$, and
--   $$
--   \{e_2,\ e_2+e_3,\ e_3,\ e_1+e_3\}\subseteq S .
--   $$
--   Then for each $i\in[n-4]$:
--
--   1. $K_i=(\mathbf 0:4,\dots,3+i,1,2,3,3+i+1,\dots,n-1)$ is a straight infeasible circuit;
--   2. $V(K_i\triangle e_n)\subseteq S$;
--   3. $\{e_2,\ e_2+e_3,\ e_3,\ e_1+e_3\}\triangle e_4\triangle\cdots\triangle e_{3+i}\subseteq S$.
--
--   The lemma is the inductive engine behind Proposition 5.3.
--
--   **Formalization Note** The coordinate sequence of $K_i$ is written with 0-based positions $p$: it sends $p<i$ to the index $p+3$, $i\le p<i+3$ to $p-i$, and $p\ge i+3$ to $p$, which are the paper's coordinates $4,\dots,3+i,1,2,3,4+i,\dots,n-1$.
--
--   Differences from the source:
--   - encoding: points of {0,1}ⁿ with coordinates 1, …, n → Fin n → Bool, coordinate i is the index i − 1; reason: Lean convention; same points
--   - encoding: "S has a T restriction": a series of 0/1-restrictions followed by an isomorphism (footnote 3, p.5) → HasRestriction S T: one restriction restrict S ι a fixing the coordinates outside the range of an injection ι : Fin m ↪ Fin n, with 1 ≤ m, followed by IsIso; reason: a series of 0/1-restrictions fixes a set of coordinates; ι may relabel, which IsIso allows anyway; every statement of the paper takes n ≥ 1, so 0-dimensional restrictions are never meant
--   - encoding: a straight infeasible circuit K of length 2(n − 1) contained in {x : xₙ = 0} with V(K△eₙ) ⊆ S → K = (v₀ : ι) with ι : Fin (n − 1) → Fin n and IsStraightCircuit ι; every vertex of circuitVerts v₀ ι is ∉ S, has last coordinate 0, and lifts by eₙ into S; reason: K enters the statement only through its vertex set and its length 2ℓ; same instances
-- source:
--   Abdi, Cornuéjols, Lee, Resistant sets in the unit hypercube, accepted manuscript (Oct. 28, 2019), LSE Research Online 102397, Lemma 5.2, p.24 (PDF p.25)

import Mathlib
import Definitions.Def_ResistantSets_twist
import Definitions.Def_ResistantSets_IsResistant
import Definitions.Def_ResistantSets_IsPolar
import Definitions.Def_ResistantSets_HasRestriction
import Definitions.Def_ResistantSets_Rk1
import Definitions.Def_ResistantSets_R5
import Definitions.Def_ResistantSets_circuitVerts

namespace ResistantSets

/-- **Lemma 5.2** (Abdi, Cornuéjols, Lee, *Resistant sets in the unit hypercube*, accepted manuscript (Oct. 28, 2019), p.24): "Take an integer n ≥ 6 and a resistant set S ⊆ {0,1}ⁿ without
antipodal points and without an R1,1, R5 restriction. Suppose K := (0 : 1, 2, 3, 4, 5, …, n − 1)
is a straight infeasible circuit, V(K△eₙ) ⊆ S, and {e₂, e₂ + e₃, e₃, e₁ + e₃} ⊆ S. Then, for each
i ∈ [n − 4], Kᵢ := (0 : 4, …, 3 + i, 1, 2, 3, 3 + i + 1, …, n − 1) is a straight infeasible
circuit, V(Kᵢ△eₙ) ⊆ S and {e₂, e₂ + e₃, e₃, e₁ + e₃}△e₄△⋯△e_{3+i} ⊆ S."

**Formalization Note** Paper coordinate `j` is the index `j − 1`. `K` is
`circuitVerts 0 (stdSeq n)`. The sequence of `Kᵢ` sends position `p` (0-indexed) to
`p + 3` for `p < i`, to `p − i` for `i ≤ p < i + 3`, and to `p` otherwise, i.e. to the
paper's coordinates `4, …, 3 + i, 1, 2, 3, 4 + i, …, n − 1`. The point `e₂ + e₃` is
`χ{2, 3}` and twisting by `e₄△⋯△e_{3+i}` flips the indices `3, …, 2 + i`. -/
theorem lemma_5_2 {n : ℕ} (hn : 6 ≤ n) (S : Finset (Fin n → Bool)) (hS : IsResistant S)
    (hanti : ¬ HasAntipodal S) (hR11 : ¬ HasRestriction S (Rk1 1))
    (hR5 : ¬ HasRestriction S R5)
    (hKinf : ∀ w ∈ circuitVerts (fun _ => false) (stdSeq n), w ∉ S)
    (hKlift : ∀ w ∈ circuitVerts (fun _ => false) (stdSeq n),
      vxor w (unitVec (lastCoord n (by omega))) ∈ S)
    (hpts : ∀ P ∈ ({fun j => decide (j.val = 1), fun j => decide (j.val = 1 ∨ j.val = 2),
        fun j => decide (j.val = 2), fun j => decide (j.val = 0 ∨ j.val = 2)} :
          Finset (Fin n → Bool)), P ∈ S) :
    ∀ i : ℕ, 1 ≤ i → ∀ hi : i ≤ n - 4,
      let Ki : Fin (n - 1) → Fin n := fun p =>
        ⟨if p.val < i then p.val + 3 else if p.val < i + 3 then p.val - i else p.val, by
          have := p.isLt; split_ifs <;> omega⟩
      IsStraightCircuit Ki ∧
      (∀ w ∈ circuitVerts (fun _ => false) Ki, w ∉ S) ∧
      (∀ w ∈ circuitVerts (fun _ => false) Ki, vxor w (unitVec (lastCoord n (by omega))) ∈ S) ∧
      (∀ P ∈ ({fun j => decide (j.val = 1), fun j => decide (j.val = 1 ∨ j.val = 2),
          fun j => decide (j.val = 2), fun j => decide (j.val = 0 ∨ j.val = 2)} :
            Finset (Fin n → Bool)),
        vxor P (fun j => decide (3 ≤ j.val ∧ j.val ≤ 2 + i)) ∈ S) := by sorry

end ResistantSets
