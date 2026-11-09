-- Prove2me | Theorems.Thm_ThreeColorFloodIt_FixedHeight_alternating_chain
-- name    : ThreeColorFloodIt.FixedHeight.alternating_chain
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:52:11.209737+00:00
-- url     : https://prove2.me/theorems/6355821f-4cea-4a0f-89da-a76250b8377d
-- title:
--   Lemma 13 — Alternating skeleton chains
-- statement:
--   Let $K$ be a local template on a connected named window. On a skeleton edge with internal node list $x_0,\ldots,x_{t-1}$, all internal nodes have the same nonempty proper descendant-mark set $L$. Some color in the target-boundary set $\operatorname{Forb}(L)$ is excluded throughout the chain. Consequently there are colors $a,b$ with
--   $$c(x_i)=\begin{cases}a&i\text{ even},\\b&i\text{ odd}.\end{cases}$$
--   The internal word may be empty; no length bound or condition equating the forbidden color to the upper endpoint is imposed. This is the source of polynomially many bounded-budget chain descriptions.
--
--   Differences from the source:
--   - encoding: finite graphs, vertices, colors and finite rooted trees → Mathlib simple graphs, finite named carriers, a shared rooted-tree model and explicit legal-sequence predicates; reason: the same source instances are represented; unused palette colors and unowned tree nodes remain allowed
--   - generalization: all internal nodes of a nonempty skeleton chain avoid a common color → for every skeleton chain, including one with empty internal word, a common avoided color taken from Forb(L_b), and every internal node has descendant-mark set L_b; reason: these are the facts the source proof establishes; the source's statement is the instance with a nonempty internal word and forgets which color is avoided
-- source:
--   Zhou, Three-Color Free-Flood-It on Fixed-Height Grids Is Polynomial-Time Solvable, STOC 2027 submission #31, supplied 2026 preprint, SHA-256 222ec38f7c30952eda9e86f87b16e8d7dfc93aa0b6b9705ac931e1b56017d280, printed p. 9 (PDF 10), Lemma 13; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/31.pdf

import Definitions.Def_ThreeColorFloodIt_FixedHeight_trees

set_option autoImplicit false

namespace ThreeColorFloodIt.FixedHeight

theorem alternating_chain {s : ℕ} (G : SimpleGraph (Fin s)) (f : Fin s → Fin 3)
    (connected : ConnectedSet G Set.univ) (K : TreeData (Fin s) (Fin 3))
    (template : LocalTemplate G f K) (a b : Fin K.tree.size)
    (xs : List (Fin K.tree.size)) (chain : SkeletonChain K xs a b) :
    (∃ c ∈ Forbidden G f (Region K b), ∀ x ∈ xs, K.color x ≠ c) ∧
    (∀ x ∈ xs, Region K x = Region K b) ∧
    ∃ c d : Fin 3, ∀ i : Fin xs.length,
      K.color (xs.get i) = if i.val % 2 = 0 then c else d := by sorry

end ThreeColorFloodIt.FixedHeight
