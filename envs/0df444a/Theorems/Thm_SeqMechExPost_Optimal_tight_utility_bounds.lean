-- Prove2me | Theorems.Thm_SeqMechExPost_Optimal_tight_utility_bounds
-- name    : SeqMechExPost.Optimal.tight_utility_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:18:11.720134+00:00
-- url     : https://prove2.me/theorems/6c737e58-ced8-47da-863d-9dc6c1a97077
-- title:
--   §3.1, p. 9 — every feasible solution of the adjusted problem can be modified so that all utility bounds (13) before the last day bind, with the same objective
-- statement:
--   Let $(x,\hat p)$ be a feasible solution of the adjusted problem (11)–(13). Then there is a feasible solution $(x,\hat q)$ with the same allocations and the same objective value (11) in which every utility bound (13) before the last day holds with equality:
--   $$v_i x_i(v_{\le i}) - \hat q_i(v_{\le i}) = \mathbf E_{v_{i+1}}\big[x_{i+1}(v_{\le i+1})v_{i+1} - \hat q_{i+1}(v_{\le i+1})\big] \qquad \text{for all } i < k \text{ and all type profiles}.$$
--   In particular, the adjusted problem has an optimal solution in which all these bounds bind.
--
--   This structural observation opens §3.1 and is the step from Lemma 3 to Lemma 4: binding bounds mean the buyer is charged his full surplus on every day but the last.
--
--   **Formalization Note** Days are 0-based; "before the last day" is Lean day $i$ with $i + 1 < k$. Equality is required on every type profile.
-- source:
--   Ashlagi, Daskalakis, Haghpanah, Sequential Mechanisms with ex-post Participation Guarantees, arXiv:1603.07229v2, p. 9 (PDF 10), §3.1, opening paragraph

import Mathlib
import Definitions.Def_SeqMechExPost_Optimal_Model
import Definitions.Def_SeqMechExPost_Optimal_Tradeoff

namespace SeqMechExPost.Optimal

theorem tight_utility_bounds {k : ℕ} (I : Instance k) :
    (∀ A : AdjMech k, A.AdjFeasible I →
      ∃ A' : AdjMech k, A'.AdjFeasible I ∧ A'.x = A.x ∧ A'.adjObj I = A.adjObj I ∧
        ∀ i v, I.InBox v → i.val + 1 < k →
          v i * A'.x i v - A'.pHat i v = A'.nextU I i v) ∧
    (∃ A : AdjMech k, A.AdjOptimal I ∧
      ∀ i v, I.InBox v → i.val + 1 < k →
        v i * A.x i v - A.pHat i v = A.nextU I i v) := by sorry

end SeqMechExPost.Optimal
