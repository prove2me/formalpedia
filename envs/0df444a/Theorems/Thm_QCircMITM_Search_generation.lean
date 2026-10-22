-- Prove2me | Theorems.Thm_QCircMITM_Search_generation
-- name    : QCircMITM.Search.generation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:39:09.080824+00:00
-- url     : https://prove2.me/theorems/a5fd188e-2a71-493c-921f-3376d129b93a
-- title:
--   §3, p. 6 — S_i is exactly the set of unitaries of the circuits of i layers
-- statement:
--   Let $V \subseteq U(2^n)$ be a finite set of unitaries, standing for $\mathcal V_{n,\mathcal G}$. For every $i \ge 0$:
--
--   1. a list $c$ of unitaries is a circuit of $i$ layers over $V$ (as generated recursively by MITM-factor, extending circuits of $i-1$ layers by one more layer) if and only if $c$ has length $i$ and all its entries lie in $V$;
--   2. the set $S_i = VS_{i-1}$ ($S_0 = \{I\}$) built by MITM-factor is exactly the set of unitaries implemented by these circuits:
--   $$S_i = \{\, U_1U_2\cdots U_i : U_1,\dots,U_i \in V \,\}.$$
--
--   So the sets the algorithm generates step by step are the sets "$S_i$ of all unitaries implementable in depth $i$" of Lemma 1, and the circuits it extends are all depth-$i$ circuits.
--
--   **Formalization Note.** A circuit is a `List` of layers and implements its `List.prod`, with the head of the list leftmost, as in "$U_1U_2\cdots U_m$" on p. 4.
-- source:
--   Amy, Maslov, Mosca, Roetteler, A meet-in-the-middle algorithm for fast synthesis of depth-optimal quantum circuits, arXiv:1206.0758v3, p. 6, §3 (paragraph after the MITM-factor pseudocode)

import Mathlib
import Definitions.Def_QCircMITM_Search_Algorithm

namespace QCircMITM.Search

theorem generation {n : ℕ} (V : Finset (Unitary n)) (i : ℕ) :
    (∀ c : List (Unitary n), c ∈ circuits V i ↔ c.length = i ∧ ∀ W ∈ c, W ∈ V) ∧
      S V i = (circuits V i).image List.prod := by sorry

end QCircMITM.Search
