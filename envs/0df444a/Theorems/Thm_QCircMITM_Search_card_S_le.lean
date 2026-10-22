-- Prove2me | Theorems.Thm_QCircMITM_Search_card_S_le
-- name    : QCircMITM.Search.card_S_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:39:19.210227+00:00
-- url     : https://prove2.me/theorems/ccdd7c46-5590-464d-a2a8-240c63f7b6f2
-- title:
--   §3, p. 6 — |S_i| ≤ |V_{n,G}|^i (the cardinality bound of the running-time analysis)
-- statement:
--   Let $V \subseteq U(2^n)$ be a finite set of unitaries, standing for $\mathcal V_{n,\mathcal G}$, and let $S_0 = \{I\}$, $S_i = VS_{i-1}$. Then for every $i \ge 0$,
--   $$|S_i| \le |V|^i .$$
--
--   This bound turns the per-iteration cost of MITM-factor, stated in terms of $|S_{i-1}|$ and $|S_i|$, into the bound $2|\mathcal V_{n,\mathcal G}|^i\log(|\mathcal V_{n,\mathcal G}|^i)$ of the running-time analysis. The time bound itself is part of the goal theorem.
--
--   **Formalization Note.** The statement holds for every finite set of unitaries $V$.
-- source:
--   Amy, Maslov, Mosca, Roetteler, A meet-in-the-middle algorithm for fast synthesis of depth-optimal quantum circuits, arXiv:1206.0758v3, p. 6, §3, running-time paragraph

import Mathlib
import Definitions.Def_QCircMITM_Search_Algorithm

namespace QCircMITM.Search

theorem card_S_le {n : ℕ} (V : Finset (Unitary n)) (i : ℕ) :
    (S V i).card ≤ V.card ^ i := by sorry

end QCircMITM.Search
