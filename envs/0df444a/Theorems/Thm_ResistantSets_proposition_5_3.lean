-- Prove2me | Theorems.Thm_ResistantSets_proposition_5_3
-- name    : ResistantSets.proposition_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:28:34.290838+00:00
-- url     : https://prove2.me/theorems/064f508f-1177-4401-bf26-2eab88b1eee1
-- title:
--   Proposition 5.3 — no $D_3$ restriction with its infeasible points on $K$
-- statement:
--   Let $D_3=\{000,100,110,111\}$. Let $n\ge5$ and let $S\subseteq\{0,1\}^n$ be a resistant set without antipodal points and without an $R_{1,1}$ or $R_5$ restriction. Let $K$ be a straight infeasible circuit of length $2(n-1)$ contained in $\{x : x_n=0\}$ such that $V(K\triangle e_n)\subseteq S$. Then $S$ does not have a $D_3$ restriction whose infeasible points all belong to $K$.
--
--   Precisely: there is no 3-dimensional face of $\{0,1\}^n$ (free coordinates $\kappa_1,\kappa_2,\kappa_3$, the others fixed) and twist $t\in\{0,1\}^3$ such that a point $x$ of the face is feasible exactly when $(x_{\kappa_1},x_{\kappa_2},x_{\kappa_3})\triangle t\in D_3$, and every point $x$ of the face with $(x_{\kappa_1},x_{\kappa_2},x_{\kappa_3})\triangle t\notin D_3$ is a vertex of $K$.
--
--   This rules out the case $|\{0010,0110\}\cap H|=2$ in the base case of Lemma 5.4.
--
--   Differences from the source:
--   - encoding: points of {0,1}ⁿ with coordinates 1, …, n → Fin n → Bool, coordinate i is the index i − 1; reason: Lean convention; same points
--   - encoding: "S has a T restriction": a series of 0/1-restrictions followed by an isomorphism (footnote 3, p.5) → HasRestriction S T: one restriction restrict S ι a fixing the coordinates outside the range of an injection ι : Fin m ↪ Fin n, with 1 ≤ m, followed by IsIso; reason: a series of 0/1-restrictions fixes a set of coordinates; ι may relabel, which IsIso allows anyway; every statement of the paper takes n ≥ 1, so 0-dimensional restrictions are never meant
--   - encoding: a straight infeasible circuit K of length 2(n − 1) contained in {x : xₙ = 0} with V(K△eₙ) ⊆ S → K = (v₀ : ι) with ι : Fin (n − 1) → Fin n and IsStraightCircuit ι; every vertex of circuitVerts v₀ ι is ∉ S, has last coordinate 0, and lifts by eₙ into S; reason: K enters the statement only through its vertex set and its length 2ℓ; same instances
--   - encoding: a D₃ restriction whose infeasible points all belong to K → a face with free coordinates κ : Fin 3 ↪ Fin n and fixed values a, a twist t, with x ∈ S ↔ (x ∘ κ) △ t ∈ D3 on the face, and every point of the face with (x ∘ κ) △ t ∉ D3 in circuitVerts; reason: the relabeling of an isomorphic restriction is absorbed in κ; the infeasible points of the restriction, as points of {0,1}ⁿ, are these face points
-- source:
--   Abdi, Cornuéjols, Lee, Resistant sets in the unit hypercube, accepted manuscript (Oct. 28, 2019), LSE Research Online 102397, Proposition 5.3, p.27 (PDF p.28)

import Mathlib
import Definitions.Def_ResistantSets_twist
import Definitions.Def_ResistantSets_IsResistant
import Definitions.Def_ResistantSets_IsPolar
import Definitions.Def_ResistantSets_HasRestriction
import Definitions.Def_ResistantSets_Rk1
import Definitions.Def_ResistantSets_R5
import Definitions.Def_ResistantSets_circuitVerts
import Definitions.Def_ResistantSets_D3

namespace ResistantSets

/-- **Proposition 5.3** (Abdi, Cornuéjols, Lee, *Resistant sets in the unit hypercube*, accepted manuscript (Oct. 28, 2019), p.27): "Let D3 := {000, 100, 110, 111} ⊆ {0,1}³. […] Take an
integer n ≥ 5 and a resistant set S ⊆ {0,1}ⁿ without antipodal points and without an R1,1, R5
restriction. Let K be a straight infeasible circuit of length 2(n − 1) contained in
{x : xₙ = 0} such that V(K△eₙ) ⊆ S. Then S does not have a D3 restriction whose infeasible
points all belong to K."

**Formalization Note** A `D₃` restriction is a 3-dimensional face of `{0,1}ⁿ`, with free
coordinates `κ 0, κ 1, κ 2` and the other coordinates fixed to `a`, together with a twist `t`,
such that a point `x` of the face is feasible iff `(x ∘ κ) △ t ∈ D₃` (the relabeling allowed by
an isomorphic restriction is absorbed in `κ`). Its infeasible points are the points `x` of the
face with `(x ∘ κ) △ t ∉ D₃`; "all belong to K" means that each is a vertex of `K`. Coordinate
`n` is the index `n − 1` (`lastCoord`). -/
theorem proposition_5_3 {n : ℕ} (hn : 5 ≤ n) (S : Finset (Fin n → Bool)) (hS : IsResistant S)
    (hanti : ¬ HasAntipodal S) (hR11 : ¬ HasRestriction S (Rk1 1))
    (hR5 : ¬ HasRestriction S R5) (v₀ : Fin n → Bool) (ι : Fin (n - 1) → Fin n)
    (hK : IsStraightCircuit ι)
    (hKinf : ∀ w ∈ circuitVerts v₀ ι, w ∉ S)
    (hKplane : ∀ w ∈ circuitVerts v₀ ι, w (lastCoord n (by omega)) = false)
    (hKlift : ∀ w ∈ circuitVerts v₀ ι, vxor w (unitVec (lastCoord n (by omega))) ∈ S) :
    ¬ ∃ (κ : Fin 3 ↪ Fin n) (a : Fin n → Bool) (t : Fin 3 → Bool),
      ∀ x : Fin n → Bool, (∀ j, (∀ k, κ k ≠ j) → x j = a j) →
        (x ∈ S ↔ vxor (fun k => x (κ k)) t ∈ D3) ∧
        (vxor (fun k => x (κ k)) t ∉ D3 → x ∈ circuitVerts v₀ ι) := by sorry

end ResistantSets
