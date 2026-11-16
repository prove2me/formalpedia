-- Prove2me | Theorems.Thm_RGMISFast_root_connected_tree_code_exists
-- name    : RGMISFast.root_connected_tree_code_exists
-- status  : Open
-- author  : @srikkanthr
-- created : 2026-11-15T22:27:24.087723+00:00
-- url     : https://prove2.me/theorems/2cd6e742-5c4d-4011-a0e9-72b54ff0a27a
-- title:
--   Every root-connected set has a depth-first spanning-tree code
-- statement:
--   Let a finite simple graph have every degree at most $\Delta$, and fix a root. Every root-connected vertex set $A$ of size $j+1$ is the decoded visited set of some traversal code with $2j$ binary descent/return commands and $j$ neighbour indices, each smaller than $\Delta$.
--
--   This is the spanning-tree encoding step in the proof of Lemma A.2. It is a structural existence statement about the explicit decoder; the bound on the number of codes is proved separately. There is no lower bound on $\Delta$ or $j$.
--
--   **Formalization note.** The ordered tree in the paper is represented by its depth-first binary word and edge labels. The conclusion asserts decoding completeness, rather than introducing an abstract injection based on a cardinality assumption.
-- source:
--   Dalirrooyfard, Makarychev, Mitrović, Ramachandran, Randomized Greedy MIS Is Fast at Every Node, Appendix A, proof of Lemma A.2, printed p.29 (PDF p.31), manuscript sha256 e93cdfecc03618969d5f2ecf8171c6f84c528edcc473b2f864299e555f823664.

import Definitions.Def_RGMISFast_rootedTreeCode
import Definitions.Def_RGMISFast_IsRootConnected
open RGMISFast
set_option autoImplicit false

theorem RGMISFast.root_connected_tree_code_exists {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ)
    (hdeg : ∀ v, G.degree v ≤ Δ) (u : V) (j : ℕ)
    (A : Finset V) (hA : IsRootConnected G u A) (hcard : A.card = j+1) :
    ∃ (shape : Fin (2*j) → Bool) (labels : Fin j → Fin Δ),
      rootedTreeCode G Δ u j shape labels = A := by sorry
