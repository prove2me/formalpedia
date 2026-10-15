-- Prove2me | Theorems.Thm_PrizeAlloc_Interval_lemma_1
-- name    : PrizeAlloc.Interval.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:29:36.859351+00:00
-- url     : https://prove2.me/theorems/c415d58a-1592-40a2-9db9-2197aea434fd
-- title:
--   Lemma 1 — endowment monotonicity implies endowment continuity
-- statement:
--   Let $\varphi$ be a prize allocation rule. If $\varphi$ satisfies endowment monotonicity, that is, $\varphi_i(N, \mathcal R, E) \le \varphi_i(N, \mathcal R, E')$ whenever $E < E'$, then it satisfies endowment continuity: for every ranked set of competitors $(N, \mathcal R)$ and every $i \in N$,
--   $$E \mapsto \varphi_i(N, \mathcal R, E) \ \text{ is continuous on } \mathbb R_+.$$
--
--   The lemma lets every later argument move the endowment continuously; it is used in the proofs of Lemma 2, Theorem 1 and Lemma 4, and in the companion missions on local and top consistency.
--
--   **Formalization Note** Continuity is `ContinuousOn` on $[0, \infty)$ for each coordinate; rankings are duplicate-free nonempty lists.
-- source:
--   Dietzenbacher and Kondratev, Fair and Consistent Prize Allocation in Competitions, arXiv:2008.08985v2, p. 10, Lemma 1 (proof p. 24)

import Mathlib
import Definitions.Def_PrizeAlloc_Interval_Setting

namespace PrizeAlloc.Interval

theorem lemma_1 {U : Type*} [DecidableEq U] (φ : List U → ℝ → U → ℝ) (hφ : IsPrizeRule φ)
    (hEM : EndowmentMonotone φ) : EndowmentContinuous φ := by sorry

end PrizeAlloc.Interval
