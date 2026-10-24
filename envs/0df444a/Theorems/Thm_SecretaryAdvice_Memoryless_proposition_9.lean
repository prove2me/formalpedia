-- Prove2me | Theorems.Thm_SecretaryAdvice_Memoryless_proposition_9
-- name    : SecretaryAdvice.Memoryless.proposition_9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T00:43:02.656362+00:00
-- url     : https://prove2.me/theorems/941fd22c-03fd-4c19-98ff-d5e227bd9e45
-- title:
--   Proposition 9, p. 10 — under NF and HI every policy yields feasible LP values z(i,s) whose objective (5) is its success probability
-- statement:
--   Let $\mathbb P$ be a signaling structure on $n$ secretaries with finite signal space $\mathcal S$ that satisfies Non-Filtering and History-Irrelevance, and let $q$ be any policy. Then there are values $z(i,s)\ge 0$, for $i\in[n]$ and $s\in\mathcal S$, satisfying constraint (4),
--   $$z(i,s)\le 1-\sum_{j<i}\sum_{s'\in\mathcal S} z(j,s')\,c(i,s,j,s'),$$
--   such that the objective (5) equals the probability that $q$ selects the highest ranked secretary:
--   $$\sum_{i=1}^n\sum_{s\in\mathcal S} z(i,s)\,a(i,s)=\mathbb P[q \text{ stops at an } i \text{ with } r_i=n].$$
--
--   Together with Proposition 10 it shows that the LP of §3 describes exactly the achievable success probabilities, which is the route to Theorem 8.
--
--   **Formalization Note** Secretaries are indexed by `Fin n`, 0-based: Lean index $i$ is the paper's secretary $i+1$, and Lean rank $r$ is the paper's rank $r+1$, so the paper's top rank $n$ is Lean rank $n-1$. The statement is for every valid policy, as on the page. The paper's derivation takes $z(i,s)=\mathbb P[i\text{ is picked}\mid T_i,s_i=s]$ for a policy that picks only best-so-far secretaries (the normal form of §2, p. 6); the statement here does not assume that normal form, since the paper's Proposition 9 quantifies over all policies.
-- source:
--   Dütting et al., Secretaries with Advice, arXiv:2011.06726v1, p. 10, Proposition 9

import Mathlib
import Definitions.Def_SecretaryAdvice_Memoryless_Setting
import Definitions.Def_SecretaryAdvice_Memoryless_LP

namespace SecretaryAdvice.Memoryless

/-- Proposition 9, p. 10: under NF and HI, every policy has LP values `z(i, s) ≥ 0` satisfying
(4) whose objective (5) equals the policy's probability of selecting the top secretary. -/
theorem proposition_9 {n : ℕ} {S : Type} [Fintype S] (μ : SignalingStructure n S)
    (hNF : NonFiltering μ) (hHI : HistoryIrrelevance μ) (q : Policy n S) (hq : ValidPolicy q) :
    ∃ z : Fin n → S → ℝ, LPFeasible μ z ∧ LPObj μ z = win μ q := by sorry

end SecretaryAdvice.Memoryless
