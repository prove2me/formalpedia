-- Prove2me | Theorems.Thm_ResistantSets_lemma_5_4
-- name    : ResistantSets.lemma_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:28:54.270141+00:00
-- url     : https://prove2.me/theorems/4b8579cc-2d13-42c2-9111-39394b8951b7
-- title:
--   Lemma 5.4 — $(\diamond)$ and the hypercube property spread from $\{x_{\ell+1}=\dots=x_n=0\}$ to $\{x_{\ell+2}=\dots=x_n=0\}$
-- statement:
--   Let $n\ge5$ and let $S\subseteq\{0,1\}^n$ be a resistant set without antipodal points, and let $K=(\mathbf 0:1,2,\dots,n-1)$ be a straight infeasible circuit such that $V(K\triangle e_n)\subseteq S$. Suppose that $\ell\in\{2,\dots,n-3\}$ is such that the points of $\{x : x_{\ell+1}=\cdots=x_n=0\}$ satisfy $(\diamond)$ and the feasible points in there form a hypercube. Then one of the following holds:
--
--   1. $S$ has one of $\{R_{k,1} : 1\le k\le\ell\}\cup\{R_5\}$ as a restriction;
--   2. the points of $\{x : x_{\ell+2}=\cdots=x_n=0\}$ satisfy $(\diamond)$ and the feasible points in there form a hypercube.
--
--   Iterating the lemma for $\ell=2,\dots,n-3$ is the core of the proof of Theorem 5.5.
--
--   **Formalization Note** With 0-based indices, $\{x : x_{\ell+1}=\cdots=x_n=0\}$ is the set of points vanishing at every index $j\ge\ell$.
--
--   Differences from the source:
--   - encoding: points of {0,1}ⁿ with coordinates 1, …, n → Fin n → Bool, coordinate i is the index i − 1; reason: Lean convention; same points
--   - encoding: "S has a T restriction": a series of 0/1-restrictions followed by an isomorphism (footnote 3, p.5) → HasRestriction S T: one restriction restrict S ι a fixing the coordinates outside the range of an injection ι : Fin m ↪ Fin n, with 1 ≤ m, followed by IsIso; reason: a series of 0/1-restrictions fixes a set of coordinates; ι may relabel, which IsIso allows anyway; every statement of the paper takes n ≥ 1, so 0-dimensional restrictions are never meant
--   - encoding: "a hypercube" → IsHypercube T: T = ∅ or T is a face {x : xᵢ = aᵢ, i ∈ I}; reason: the paper counts the empty set (p.29, "(possibly empty) hypercube")
--   - encoding: K := (0 : 1, 2, …, n − 1) is a straight infeasible circuit with V(K△eₙ) ⊆ S → every vertex of circuitVerts 0 (stdSeq n) is ∉ S and lifts by eₙ into S; reason: the circuit (0 : 1, …, n − 1) is straight by definition; the hypothesis is its infeasibility
-- source:
--   Abdi, Cornuéjols, Lee, Resistant sets in the unit hypercube, accepted manuscript (Oct. 28, 2019), LSE Research Online 102397, Lemma 5.4, p.28 (PDF p.29)

import Mathlib
import Definitions.Def_ResistantSets_twist
import Definitions.Def_ResistantSets_IsResistant
import Definitions.Def_ResistantSets_IsPolar
import Definitions.Def_ResistantSets_HasRestriction
import Definitions.Def_ResistantSets_Rk1
import Definitions.Def_ResistantSets_R5
import Definitions.Def_ResistantSets_circuitVerts
import Definitions.Def_ResistantSets_Diamond
import Definitions.Def_ResistantSets_IsHypercube

namespace ResistantSets

/-- **Lemma 5.4** (Abdi, Cornuéjols, Lee, *Resistant sets in the unit hypercube*, accepted manuscript (Oct. 28, 2019), p.28): "Take an integer n ≥ 5 and a resistant set S ⊆ {0,1}ⁿ that does
not have antipodal points, and let K := (0 : 1, 2, …, n − 1) be a straight infeasible circuit such
that V(K△eₙ) ⊆ S. Suppose that ℓ ∈ {2, …, n − 3} is an integer such that the points in
{x : x_{ℓ+1} = ⋯ = xₙ = 0} satisfy (⋄) and the feasible points in there form a hypercube. Then
one of the following statements hold: • S has one of {R_{k,1} : 1 ≤ k ≤ ℓ} ∪ {R5} as a
restriction, or • the points in {x : x_{ℓ+2} = ⋯ = xₙ = 0} satisfy (⋄) and the feasible points in
there form a hypercube."

**Formalization Note** Paper coordinate `j` is the index `j − 1`, so `{x : x_{ℓ+1} = ⋯ = xₙ = 0}`
is `{x : x j = false for every index j ≥ ℓ}`. "The feasible points in there form a hypercube" is
`IsHypercube` of `S` intersected with that face (possibly empty, p.29). -/
theorem lemma_5_4 {n : ℕ} (hn : 5 ≤ n) (S : Finset (Fin n → Bool)) (hS : IsResistant S)
    (hanti : ¬ HasAntipodal S)
    (hKinf : ∀ w ∈ circuitVerts (fun _ => false) (stdSeq n), w ∉ S)
    (hKlift : ∀ w ∈ circuitVerts (fun _ => false) (stdSeq n),
      vxor w (unitVec (lastCoord n (by omega))) ∈ S)
    (ℓ : ℕ) (hℓ₁ : 2 ≤ ℓ) (hℓ₂ : ℓ ≤ n - 3)
    (hdia : ∀ x : Fin n → Bool, (∀ j : Fin n, ℓ ≤ j.val → x j = false) →
      Diamond S (lastCoord n (by omega)) x)
    (hcube : IsHypercube (S.filter fun x => ∀ j : Fin n, ℓ ≤ j.val → x j = false)) :
    ((∃ k : ℕ, 1 ≤ k ∧ k ≤ ℓ ∧ HasRestriction S (Rk1 k)) ∨ HasRestriction S R5) ∨
      ((∀ x : Fin n → Bool, (∀ j : Fin n, ℓ + 1 ≤ j.val → x j = false) →
          Diamond S (lastCoord n (by omega)) x) ∧
        IsHypercube (S.filter fun x => ∀ j : Fin n, ℓ + 1 ≤ j.val → x j = false)) := by sorry

end ResistantSets
