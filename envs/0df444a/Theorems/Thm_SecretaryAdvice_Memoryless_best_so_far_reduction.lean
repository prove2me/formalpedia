-- Prove2me | Theorems.Thm_SecretaryAdvice_Memoryless_best_so_far_reduction
-- name    : SecretaryAdvice.Memoryless.best_so_far_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T00:41:50.698989+00:00
-- url     : https://prove2.me/theorems/239788b2-22d5-4c4c-a982-5bde625f615f
-- title:
--   §2, p. 6 — without loss of optimality a policy picks secretary i only if it is best so far
-- statement:
--   Let $\mathbb P$ be a signaling structure on $n$ secretaries with finite signal space $\mathcal S$, and let $q$ be any policy (at each round $i$ a stopping probability in $[0,1]$ that depends on the information $(\preceq_{1..i},s_1,\dots,s_i)$ only). Then there is a policy $q'$ that never stops at a round $i$ at which $T_i$ fails, i.e.
--   $$q'_i(x)=0\quad\text{whenever the information } x \text{ says that } i \text{ is not best so far},$$
--   and whose winning probability is at least that of $q$:
--   $$\mathbb P[q \text{ stops at a top-ranked secretary}]\le \mathbb P[q' \text{ stops at a top-ranked secretary}].$$
--
--   This is the reduction of §2 ("one can assume without loss of optimality that the algorithm only picks secretary $i$ if it is the best-so-far"), used in the derivation of constraint (4).
--
--   **Formalization Note** Secretaries are indexed by `Fin n`, 0-based: Lean index $i$ is the paper's secretary $i+1$, and Lean rank $r$ is the paper's rank $r+1$, so the paper's top rank $n$ is Lean rank $n-1$. The statement holds for every signaling structure; NF and HI are not assumed.
-- source:
--   Dütting et al., Secretaries with Advice, arXiv:2011.06726v1, p. 6, §2, paragraph after equation (1) (unnumbered claim)

import Mathlib
import Definitions.Def_SecretaryAdvice_Memoryless_Setting

namespace SecretaryAdvice.Memoryless

/-- §2, p. 6: without loss of optimality a policy picks secretary `i` only if it is best so far. -/
theorem best_so_far_reduction {n : ℕ} {S : Type} [Fintype S] (μ : SignalingStructure n S)
    (q : Policy n S) (hq : ValidPolicy q) :
    ∃ q' : Policy n S, ValidPolicy q' ∧
      (∀ (i : Fin n) (x : Info n S i), bestSoFar x = false → q' i x = 0) ∧
      win μ q ≤ win μ q' := by sorry

end SecretaryAdvice.Memoryless
