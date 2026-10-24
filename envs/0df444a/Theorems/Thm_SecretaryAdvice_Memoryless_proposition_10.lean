-- Prove2me | Theorems.Thm_SecretaryAdvice_Memoryless_proposition_10
-- name    : SecretaryAdvice.Memoryless.proposition_10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T00:42:55.645917+00:00
-- url     : https://prove2.me/theorems/2451e6e5-8f4b-44b0-b30e-67aaab2a0225
-- title:
--   Proposition 10, p. 10 — under NF and HI every feasible z(i,s) is realized by a (memoryless) policy with success probability equal to (5)
-- statement:
--   Let $\mathbb P$ be a signaling structure satisfying Non-Filtering and History-Irrelevance, and let $z(i,s)\ge 0$ satisfy constraint (4). Then there is a policy $q$ for the secretary problem whose probability of picking the highest ranked secretary equals the objective (5):
--   $$\mathbb P[q\text{ stops at an } i \text{ with } r_i=n]=\sum_{i=1}^n\sum_{s\in\mathcal S} z(i,s)\,a(i,s).$$
--   Moreover $q$ can be taken memoryless: its stopping probability at round $i$ depends only on $i$, on whether $T_i$ holds, and on $s_i$.
--
--   This is the converse of Proposition 9; the two together give Theorem 8.
--
--   **Formalization Note** Secretaries are indexed by `Fin n`, 0-based: Lean index $i$ is the paper's secretary $i+1$, and Lean rank $r$ is the paper's rank $r+1$, so the paper's top rank $n$ is Lean rank $n-1$. The memorylessness conjunct is not in the printed statement of Proposition 10; it is the observation of the proof of Theorem 8 (p. 11, "the policy we obtain from this transformation uses only $s_i, T_i$"), true of the policy (6) the proof constructs, and it is what Theorem 8 needs.
-- source:
--   Dütting et al., Secretaries with Advice, arXiv:2011.06726v1, p. 10, Proposition 10 (with the observation of the proof of Theorem 8, p. 11)

import Mathlib
import Definitions.Def_SecretaryAdvice_Memoryless_Setting
import Definitions.Def_SecretaryAdvice_Memoryless_LP

namespace SecretaryAdvice.Memoryless

/-- Proposition 10, p. 10 (with the observation of the proof of Theorem 8, p. 11, that the
constructed policy is memoryless): under NF and HI, every `z ≥ 0` satisfying (4) is realized by a
policy whose probability of selecting the top secretary equals the objective (5). -/
theorem proposition_10 {n : ℕ} {S : Type} [Fintype S] (μ : SignalingStructure n S)
    (hNF : NonFiltering μ) (hHI : HistoryIrrelevance μ) (z : Fin n → S → ℝ)
    (hz : LPFeasible μ z) :
    ∃ q : Policy n S, ValidPolicy q ∧ IsMemoryless q ∧ win μ q = LPObj μ z := by sorry

end SecretaryAdvice.Memoryless
