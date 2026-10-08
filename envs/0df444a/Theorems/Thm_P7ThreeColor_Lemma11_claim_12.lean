-- Prove2me | Theorems.Thm_P7ThreeColor_Lemma11_claim_12
-- name    : P7ThreeColor.Lemma11.claim_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:45:57.886168+00:00
-- url     : https://prove2.me/theorems/bfab66e8-8de4-4f9a-a8a7-d57de70b7020
-- title:
--   Claim 12, p. 15 — an induced path through S between two of uᵢ, vᵢ, uⱼ, vⱼ, avoiding the other two
-- statement:
--   Let $G$, $L$ and $S$ satisfy the hypotheses of Lemma 11, and for $i \in \{1,2,3\}$ let $D_i$ be the set of vertices $v \in N(S)$ with $L(v) = \{1,2,3\} \setminus \{i\}$. For a path $P$ with ends $a, b$ write $P^* = V(P) \setminus \{a,b\}$ for its interior.
--
--   Let $i \ne j$ in $\{1,2,3\}$, and let $u_i, v_i \in D_i$ and $u_j, v_j \in D_j$ be four pairwise distinct vertices such that $\{u_i, v_i, u_j, v_j\}$ is a stable set. Then there is an induced path $P$ with distinct ends $a, b \in \{u_i, v_i, u_j, v_j\}$ such that
--
--   1. $\{a,b\} \ne \{u_i,u_j\}$ and $\{a,b\} \ne \{v_i,v_j\}$;
--   2. $P^* \subseteq S$, and in particular $|L(v)| = 1$ for every $v \in P^*$;
--   3. $P^*$ is anticomplete to $\{u_i,v_i,u_j,v_j\} \setminus \{a,b\}$:
--   $$\forall z \in P^*,\ \forall w \in \{u_i,v_i,u_j,v_j\} \setminus \{a,b\}:\quad zw \notin E(G).$$
--
--   Claim 12 is the path-building step behind Claim 13: two vertices of $X_i$ whose neighbor triples are far apart would be joined through $S$ into a long induced path.
--
--   **Formalization Note** The paper states the claim for "$\{u_i,v_i,u_j,v_j\}$ is a stable set" without saying the four vertices are distinct; its proof and its only use (Claim 13: "$n_j, n_j(y), n_k, n_k(y)$ are distinct") take them pairwise distinct, and that is assumed here. The ends are required to be distinct, which excludes the degenerate one-vertex path. A path is a list of distinct vertices in which two vertices are adjacent exactly when consecutive; $P^*$ is the list with its first and last elements removed.
-- source:
--   Bonomo, Chudnovsky, Maceli, Schaudt, Stein and Zhong, Three-coloring and list three-coloring of graphs without induced paths on seven vertices, Combinatorica (2017), DOI 10.1007/s00493-017-3553-8, p. 15, Claim 12

import Mathlib
import Definitions.Def_P7ThreeColor_Lemma11_Setting
import Definitions.Def_StrongPerfectGraph_Main_IsInducedPath

namespace P7ThreeColor.Lemma11

open StrongPerfectGraph.Main in
/-- Claim 12, p. 15. Let `i ≠ j`, `u_i, v_i ∈ D_i`, `u_j, v_j ∈ D_j`, pairwise distinct, with
`{u_i, v_i, u_j, v_j}` stable. Then there is an induced path `P` with distinct ends
`a, b ∈ {u_i, v_i, u_j, v_j}` such that (a) `{a,b} ≠ {u_i,u_j}` and `{a,b} ≠ {v_i,v_j}`,
(b) `P* ⊆ S` and `|L(v)| = 1` for `v ∈ P*`, and (c) `P*` is anticomplete to
`{u_i, v_i, u_j, v_j} \ {a, b}`. Here `P*` (the interior) is `p.tail.dropLast`. -/
theorem claim_12 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (L : V → Finset (Fin 3)) (S : Finset V) (hyp : Lemma11Hyp G L S)
    (i j : Fin 3) (hij : i ≠ j) (ui vi uj vj : V)
    (hui : ui ∈ D G L S i) (hvi : vi ∈ D G L S i) (huj : uj ∈ D G L S j) (hvj : vj ∈ D G L S j)
    (hdistinct : [ui, vi, uj, vj].Nodup)
    (hstable : ∀ a ∈ ({ui, vi, uj, vj} : Finset V), ∀ b ∈ ({ui, vi, uj, vj} : Finset V),
      ¬ G.Adj a b) :
    ∃ (p : List V) (a b : V), IsInducedPath G p ∧ p.head? = some a ∧ p.getLast? = some b ∧
      a ≠ b ∧ a ∈ ({ui, vi, uj, vj} : Finset V) ∧ b ∈ ({ui, vi, uj, vj} : Finset V) ∧
      (({a, b} : Finset V) ≠ {ui, uj} ∧ ({a, b} : Finset V) ≠ {vi, vj}) ∧
      (∀ z ∈ p.tail.dropLast, z ∈ S ∧ (L z).card = 1) ∧
      (∀ z ∈ p.tail.dropLast, ∀ w ∈ ({ui, vi, uj, vj} : Finset V) \ {a, b},
        ¬ G.Adj z w) := by sorry

end P7ThreeColor.Lemma11
