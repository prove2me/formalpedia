-- Prove2me | Theorems.Thm_SeqMechExPost_Optimal_lemma_4
-- name    : SeqMechExPost.Optimal.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:18:23.573981+00:00
-- url     : https://prove2.me/theorems/8b03c607-dda8-4b01-a92b-23670b5a87e2
-- title:
--   Lemma 4, p. 9 — some optimal mechanism charges the full surplus p_i = v_i x_i on every day before the last (zero stage utility)
-- statement:
--   1. Every feasible mechanism $(x,p)$ of the original problem (PIC (1), ex-post IR (2)) can be replaced by a feasible mechanism $(x,p')$ with the same allocations and the same revenue (3) such that
--   $$p'_i(v_{\le i}) = v_i\,x_i(v_{\le i}) \qquad \text{for all } i < k \text{ and all type profiles},$$
--   that is, the buyer's stage utility is zero on every day before the last.
--
--   2. The original problem has an optimal solution $(x,p)$ with $p_i(v_{\le i}) = v_i x_i(v_{\le i})$ for all $i < k$.
--
--   Restricting attention to mechanisms that extract the full surplus before the last day is therefore without loss of generality for revenue maximization.
--
--   **Formalization Note** Days are 0-based; "$i < k$" is Lean day $i$ with $i + 1 < k$. The existence conclusion is unconditional, as in Lemma 4. The construction for every feasible mechanism is stated separately.
-- source:
--   Ashlagi, Daskalakis, Haghpanah, Sequential Mechanisms with ex-post Participation Guarantees, arXiv:1603.07229v2, p. 9 (PDF 10), Lemma 4

import Mathlib
import Definitions.Def_SeqMechExPost_Optimal_Model
import Definitions.Def_SeqMechExPost_Optimal_Tradeoff

namespace SeqMechExPost.Optimal

theorem lemma_4 {k : ℕ} (I : Instance k) :
    (∃ M : SeqMech k, M.IsOptimal I ∧
      ∀ i v, I.InBox v → i.val + 1 < k → M.p i v = v i * M.x i v) ∧
    (∀ M : SeqMech k, M.Feasible I →
      ∃ M' : SeqMech k, M'.Feasible I ∧ M'.x = M.x ∧ M'.revenue I = M.revenue I ∧
        ∀ i v, I.InBox v → i.val + 1 < k → M'.p i v = v i * M'.x i v) := by sorry

end SeqMechExPost.Optimal
