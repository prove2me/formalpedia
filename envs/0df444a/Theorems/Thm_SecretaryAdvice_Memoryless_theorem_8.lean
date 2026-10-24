-- Prove2me | Theorems.Thm_SecretaryAdvice_Memoryless_theorem_8
-- name    : SecretaryAdvice.Memoryless.theorem_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T00:42:09.834517+00:00
-- url     : https://prove2.me/theorems/6b38238d-d9d4-4d8d-a50c-a3b1450a85ae
-- title:
--   Theorem 8, p. 9 — under Non-Filtering and History-Irrelevance an optimal stopping policy is memoryless
-- statement:
--   Let $\mathbb P$ be a signaling structure for the secretary problem with advice on $n$ secretaries with a finite signal space $\mathcal S$. If $\mathbb P$ satisfies Non-Filtering (Definition 6) and History-Irrelevance (Definition 7), then the optimal policy is memoryless: there is a memoryless policy $m$, whose stopping probability at round $i$ depends only on $i$, on whether $i$ is best so far ($T_i$), and on the signal $s_i$, such that for every policy $q$ (any randomized function of the information $(\preceq_{1..i},s_1,\dots,s_i)$ at each round)
--   $$\mathbb P[q\text{ stops at an } i\text{ with } r_i=n]\le\mathbb P[m\text{ stops at an } i\text{ with } r_i=n].$$
--
--   Memoryless policies need to store only the current signal and one comparison bit; the theorem says that under NF and HI nothing is lost by this restriction, and it reduces the search for an optimal policy to the LP of §3.
--
--   **Formalization Note** Secretaries are indexed by `Fin n`, 0-based: Lean index $i$ is the paper's secretary $i+1$, and Lean rank $r$ is the paper's rank $r+1$, so the paper's top rank $n$ is Lean rank $n-1$. The paper presupposes that an optimal policy exists; the statement asserts it (an optimal policy exists and can be chosen memoryless), which holds because, with $\mathcal S$ finite, the memoryless policies form a compact cube on which the winning probability is continuous. The competitors $q$ range over all randomized policies.
-- source:
--   Dütting et al., Secretaries with Advice, arXiv:2011.06726v1, p. 9, Theorem 8 (proof p. 11)

import Mathlib
import Definitions.Def_SecretaryAdvice_Memoryless_Setting

namespace SecretaryAdvice.Memoryless

/-- Theorem 8, p. 9: if a signaling structure satisfies Non-Filtering and History-Irrelevance,
then the optimal policy is memoryless: some valid memoryless policy has a winning probability at
least that of every valid policy. -/
theorem theorem_8 {n : ℕ} {S : Type} [Fintype S] (μ : SignalingStructure n S)
    (hNF : NonFiltering μ) (hHI : HistoryIrrelevance μ) :
    ∃ m : Policy n S, ValidPolicy m ∧ IsMemoryless m ∧
      ∀ q : Policy n S, ValidPolicy q → win μ q ≤ win μ m := by sorry

end SecretaryAdvice.Memoryless
