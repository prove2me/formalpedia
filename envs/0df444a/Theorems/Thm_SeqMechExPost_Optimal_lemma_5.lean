-- Prove2me | Theorems.Thm_SeqMechExPost_Optimal_lemma_5
-- name    : SeqMechExPost.Optimal.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:18:35.163427+00:00
-- url     : https://prove2.me/theorems/44e383a4-2d3a-49c3-8057-2ba7e2fa8609
-- title:
--   Lemma 5, p. 11 — the optimum adjusted objective with a feasible prefix fixed equals the continuation expression (15)
-- statement:
--   Let $\hat g_1,\dots,\hat g_{k+1}$ be the cumulative tradeoff functions of Definition 2 and, for an adjusted mechanism $(x,\hat p)$ and a day $j \in [1:k]$, let
--   $$V_j(x,\hat p) = \mathbf E_{v_1,\dots,v_j}\Big[\hat p_1(v_1) + \sum_{2\le i\le j} x_i(v_{\le i})v_i + \hat g_{j+1}\big(v_j x_j(v_{\le j}) - \hat p_j(v_{\le j})\big)\Big]. \quad (15)$$
--
--   For every feasible adjusted mechanism $(x,\hat p)$ and every day $j$, fixing the rules of days $1,\dots,j$ leaves a feasible completion whose objective equals $V_j(x,\hat p)$; every other feasible completion has objective at most that value. Thus (15) is the attained optimum over all completions of the prefix.
--
--   **Formalization Note** Days are 0-based: Lean day $j$ is paper day $j+1$ and `gNext I j` is the finite branch of $\hat g_{j+2}$ on non-negative states. Prefix agreement is required on every type profile, and the existential completion states attainment explicitly, as the page's “optimum value” does. No optimizer family is assumed in this statement.
-- source:
--   Ashlagi, Daskalakis, Haghpanah, Sequential Mechanisms with ex-post Participation Guarantees, arXiv:1603.07229v2, p. 11 (PDF 12), Lemma 5, (15)

import Mathlib
import Definitions.Def_SeqMechExPost_Optimal_Model
import Definitions.Def_SeqMechExPost_Optimal_Tradeoff

namespace SeqMechExPost.Optimal

theorem lemma_5 {k : ℕ} (I : Instance k) :
    ∀ A : AdjMech k, A.AdjFeasible I → ∀ j : Fin k,
      ∃ B : AdjMech k,
        B.AdjFeasible I ∧
        (∀ i : Fin k, i ≤ j → ∀ v, I.InBox v →
          B.x i v = A.x i v ∧ B.pHat i v = A.pHat i v) ∧
        B.adjObj I = contValue I A j ∧
        (∀ C : AdjMech k, C.AdjFeasible I →
          (∀ i : Fin k, i ≤ j → ∀ v, I.InBox v →
            C.x i v = A.x i v ∧ C.pHat i v = A.pHat i v) →
          C.adjObj I ≤ B.adjObj I) := by sorry

end SeqMechExPost.Optimal
