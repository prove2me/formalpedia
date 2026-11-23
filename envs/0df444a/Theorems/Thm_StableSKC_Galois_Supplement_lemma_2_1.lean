-- Prove2me | Theorems.Thm_StableSKC_Galois_Supplement_lemma_2_1
-- name    : StableSKC.Galois.Supplement.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T12:16:20.993258+00:00
-- url     : https://prove2.me/theorems/a31e84fb-0e7d-460a-a8df-aab0eca026b7
-- title:
--   Lemma 2.1, p. 6 — rounds in the node-line tournament: v_T(0, y) by the position of y, and v_T(x, x′) = v_T(0, y) on every line {y, x, x′}
-- statement:
--   Let the players $1, \dots, 7$ be the nodes of a Fano plane (player $0$ is not a node), let $x$ be a node, $\ell$ a line through $x$, and let $T$ be any knockout tournament on the players $0, \dots, 7$ that arises from the node-line pair $x, \ell$. Write $v_T(a, b) = i$ when players $a$ and $b$ can meet in round $i$ of $T$. Then:
--
--   1. for every node $y$,
--   $$v_T(0,y) = 1 \iff y = x,\qquad v_T(0,y) = 2 \iff y \in \ell,\ y \ne x,\qquad v_T(0,y) = 3 \iff y \notin \ell;$$
--   2. for every line $\ell' = \{y, x_1, x_2\}$ of the plane and every round $i$,
--   $$v_T(x_1, x_2) = i \iff v_T(0, y) = i.$$
--
--   The second part reduces the meeting round of any two non-zero players to the meeting round of player $0$ with the third node on their common line; it is the step on which the proof of Theorem 2.1 rests.
--
--   **Formalization Note** $v_T(a,b) = i$ is the published predicate `CanMeetIn T a b i`, and the equality of rounds in part 2 is stated as the equivalence of these predicates for every `i : ℕ` (for $i \notin \{1,2,3\}$ both sides are false). The plane is any `S : RolesForceSeven.STS 7`, node `j` being player `j + 1`. The names $x_1, x_2$ in part 2 are arbitrary nodes, not the node $x$ of the pair: this is how the proof of Theorem 2.1 uses the lemma. Since lines have three points, $\{y, x_1, x_2\}$ being a line forces the three nodes to be distinct.
--
--   Differences from the source:
--   - encoding: v_T(x, x′) = v_T(0, y) → ∀ i, CanMeetIn T x₁ x₂ i ↔ CanMeetIn T 0 y i; reason: v_T is a predicate in the published model; for distinct players exactly one round holds, so the two are the same statement
--   - encoding: the Fano plane with nodes 1..7 → any Steiner triple system on Fin 7, node j ↦ player j + 1; reason: every STS on seven points is the Fano plane up to relabelling, so the instances are exactly the labelled Fano planes
--   - reading: "the knockout tournament that arises from x, ℓ" → every seeding satisfying the p. 6 construction (leaves 0 and 1 fixed as 0,x; order within the other pairs and of the second-half pairs free); reason: the page prints both 0145 − 2376 and 0145-2367 for the same pair, and the construction does not fix the order
--   - reading: the names x, x′ in the Moreover clause → fresh nodes x₁, x₂; reason: the proof of Theorem 2.1 on pp. 7–8 applies the lemma to arbitrary distinct nonzero players, independently of the selected node of the tournament
-- source:
--   Lambers, Pendavingh & Spieksma, How to Design a Stable Serial Knockout Competition, arXiv:2211.02513v1, p. 6, Lemma 2.1

import Mathlib
import Definitions.Def_StableSKC_Galois_Model
import Definitions.Def_RolesForceSeven_sts
import Definitions.Def_StableSKC_Galois_Supplement_NodeLine

open RolesForceSeven

namespace StableSKC.Galois.Supplement
theorem lemma_2_1 (S : STS 7) (x : Fin 7) (ℓ : Finset (Fin 7)) (hℓ : ℓ ∈ S.lines) (hx : x ∈ ℓ)
    (T : Seeding 3 (Fin 8)) (hT : ArisesFrom S x ℓ T) :
    (∀ y : Fin 7,
      (CanMeetIn T 0 (nodePlayer y) 1 ↔ y = x) ∧
      (CanMeetIn T 0 (nodePlayer y) 2 ↔ y ∈ ℓ ∧ y ≠ x) ∧
      (CanMeetIn T 0 (nodePlayer y) 3 ↔ y ∉ ℓ)) ∧
    (∀ y x₁ x₂ : Fin 7, ({y, x₁, x₂} : Finset (Fin 7)) ∈ S.lines → ∀ i : ℕ,
      (CanMeetIn T (nodePlayer x₁) (nodePlayer x₂) i ↔ CanMeetIn T 0 (nodePlayer y) i)) := by sorry
end StableSKC.Galois.Supplement
