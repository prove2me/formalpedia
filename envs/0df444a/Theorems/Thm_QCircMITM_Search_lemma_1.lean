-- Prove2me | Theorems.Thm_QCircMITM_Search_lemma_1
-- name    : QCircMITM.Search.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:39:08.827992+00:00
-- url     : https://prove2.me/theorems/8e1a9bb8-9b95-4649-ac29-3a0e75c27e79
-- title:
--   Lemma 1, p. 5 — U has a depth-l circuit iff S†_{⌊l/2⌋}U ∩ S_{⌈l/2⌉} ≠ ∅
-- statement:
--   Let $V \subseteq U(2^n)$ be a finite set of unitaries, standing for $\mathcal V_{n,\mathcal G}$, and let $S_i$ be the set of unitaries implementable in depth $i$ over $V$. For every unitary $U$ and every $l \ge 0$, there is a circuit of exactly $l$ layers over $V$ implementing $U$ if and only if
--   $$S_{\lfloor l/2\rfloor}^\dagger\, U \;\cap\; S_{\lceil l/2\rceil} \neq \emptyset, \qquad S_{\lfloor l/2\rfloor}^\dagger U = \{\, X^\dagger U : X \in S_{\lfloor l/2\rfloor}\,\}.$$
--
--   This is the meet-in-the-middle observation: a depth-$l$ circuit can be found by generating only circuits of depth at most $\lceil l/2\rceil$ and looking for a collision.
--
--   **Formalization Note.** The statement is made for every finite set $V$ of unitaries; the paper's proof uses nothing else about $\mathcal V_{n,\mathcal G}$. It holds for $l = 0$ as well ($U = I$). $\lfloor l/2\rfloor$ is `l / 2` and $\lceil l/2\rceil$ is `(l + 1) / 2`.
-- source:
--   Amy, Maslov, Mosca, Roetteler, A meet-in-the-middle algorithm for fast synthesis of depth-optimal quantum circuits, arXiv:1206.0758v3, p. 5, Lemma 1

import Mathlib
import Definitions.Def_QCircMITM_Search_Algorithm

namespace QCircMITM.Search

theorem lemma_1 {n : ℕ} (V : Finset (Unitary n)) (U : Unitary n) (l : ℕ) :
    (∃ c : List (Unitary n), c.length = l ∧ (∀ W ∈ c, W ∈ V) ∧ c.prod = U) ↔
      ((S V (l / 2)).image (fun X => X⁻¹ * U) ∩ S V ((l + 1) / 2)).Nonempty := by sorry

end QCircMITM.Search
