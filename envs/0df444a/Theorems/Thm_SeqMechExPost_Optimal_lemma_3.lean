-- Prove2me | Theorems.Thm_SeqMechExPost_Optimal_lemma_3
-- name    : SeqMechExPost.Optimal.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:18:11.193487+00:00
-- url     : https://prove2.me/theorems/b6db76d6-32ec-42dc-9ee1-de14c62d54cd
-- title:
--   Lemma 3, p. 8 — (x, p) is feasible/optimal for the original problem iff (x, p̂) with p̂ = p − U is feasible/optimal for the adjusted problem; revenues agree
-- statement:
--   Consider $k$ days with independent values on type intervals, as in the model. Let $(x,p)$ be an admissible sequential mechanism and $(x,\hat p)$ its adjusted mechanism, $\hat p_i(v_{\le i}) = p_i(v_{\le i}) - U_i(v_{\le i})$ (7). Then:
--
--   1. $(x,p)$ is feasible for the original problem (PIC (1) and ex-post IR (2)) if and only if $(x,\hat p)$ is feasible for the adjusted problem ((12) and (13));
--   2. the revenue of $(x,p)$ equals the adjusted objective (11) of $(x,\hat p)$:
--   $$\mathbf E\Big[\sum_i p_i(v_{\le i})\Big] = \mathbf E\Big[\hat p_1(v_1) + \sum_{i=2}^k x_i(v_{\le i})v_i\Big];$$
--   3. $(x,p)$ is recovered from $(x,\hat p)$ by (9), $p_i(v_{\le i}) = \hat p_i(v_{\le i}) + \mathbf E_{v_{i+1}}[x_{i+1}(v_{\le i+1})v_{i+1} - \hat p_{i+1}(v_{\le i+1})]$, on every type profile;
--   4. $(x,p)$ is optimal for the original problem if and only if $(x,\hat p)$ is optimal for the adjusted problem.
--
--   Conversely, every feasible adjusted mechanism $(x,\hat p)$ yields through (9) a feasible mechanism of the original problem whose adjusted payments, computed by (7), are again $\hat p$ on every type profile.
--
--   The lemma turns the periodic incentive constraints, which couple all days, into a sequence of static incentive constraints, one per day and history.
--
--   **Formalization Note** Days are 0-based (Lean day $i$ is paper day $i+1$). Item 3 and the converse are stated pointwise on type profiles, where the conditional expectations are guaranteed to exist; mechanisms are compared on type profiles only, since the joint law gives the rest measure zero.
-- source:
--   Ashlagi, Daskalakis, Haghpanah, Sequential Mechanisms with ex-post Participation Guarantees, arXiv:1603.07229v2, p. 8 (PDF 9), Lemma 3

import Mathlib
import Definitions.Def_SeqMechExPost_Optimal_Model
import Definitions.Def_SeqMechExPost_Optimal_Tradeoff

namespace SeqMechExPost.Optimal

theorem lemma_3 {k : ℕ} (I : Instance k) :
    (∀ M : SeqMech k, M.Admissible I →
      (M.Feasible I ↔ (adjust I M).AdjFeasible I) ∧
      M.revenue I = (adjust I M).adjObj I ∧
      (∀ i v, I.InBox v → (unadjust I (adjust I M)).p i v = M.p i v) ∧
      (M.IsOptimal I ↔ (adjust I M).AdjOptimal I)) ∧
    (∀ A : AdjMech k, A.AdjFeasible I →
      (unadjust I A).Feasible I ∧
      ∀ i v, I.InBox v → (adjust I (unadjust I A)).pHat i v = A.pHat i v) := by sorry

end SeqMechExPost.Optimal
