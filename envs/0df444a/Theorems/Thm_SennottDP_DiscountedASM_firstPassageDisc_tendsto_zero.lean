-- Prove2me | Theorems.Thm_SennottDP_DiscountedASM_firstPassageDisc_tendsto_zero
-- name    : SennottDP.DiscountedASM.firstPassageDisc_tendsto_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T07:44:59.024691+00:00
-- url     : https://prove2.me/theorems/f189c009-5f9f-4e78-9ab6-f5aae8557726
-- title:
--   Lemma 4.7.3 — $E_e[\alpha^{T_i(N)}]\to 0$ for the first passage out of $S_N$
-- statement:
--   Let $\Delta$ be an MDC with countable state space $S$, $(S_N)_{N\ge N_0}$ the state spaces of an approximating sequence for $\Delta$, $\alpha\in(0,1)$, and $e$ a stationary policy of $\Delta$. Fix $i\in S$; for $N$ so large that $i\in S_N$, run the chain of $\Delta$ under $e$ from $i$ until the set $S-S_N$ is reached, and let $T_i(N)\in\{1,2,\dots\}\cup\{\infty\}$ be the number of steps in this first passage. Then
--   $$
--   \lim_{N\to\infty}E_e\big[\alpha^{T_i(N)}\big]=0,
--   $$
--   where $E_e[\alpha^{T_i(N)}]=\sum_{n\ge1}\alpha^nP(T_i(N)=n)$, i.e. $\alpha^\infty=0$.
--
--   The larger the truncated state space, the longer (in the discounted sense) the chain takes to leave it. This is the estimate that controls the error made by redirecting excess probability in Proposition 4.7.4.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 78, Lemma 4.7.3, equations (4.44)–(4.45)

import Mathlib
import Definitions.Def_SennottDP_DiscountedASM_MDC
import Definitions.Def_SennottDP_DiscountedASM_ApproxSeq
import Definitions.Def_SennottDP_DiscountedASM_tabooProb

open scoped ENNReal NNReal
open Classical Filter Topology

namespace SennottDP.DiscountedASM

/-- Lemma 4.7.3 (p. 78): operate `M` from `i` under the stationary policy `e` until
`S - S_N` is reached, and let `T_i(N)` be the length of this first passage; then
`lim_{N→∞} E_e[α^{T_i(N)}] = 0` (4.44), with `α^∞ = 0` (4.45). -/
theorem firstPassageDisc_tendsto_zero {S Act : Type} [Countable S] (M : MDC S Act)
    (Δs : ApproxSeq M) (α : ℝ≥0) (hα0 : 0 < α) (hα1 : α < 1)
    (e : S → Act) (he : ∀ i, e i ∈ M.A i) (i : S) :
    Tendsto (fun N => M.firstPassageDisc (Δs.SN N) e α i) atTop (𝓝 0) := by sorry

end SennottDP.DiscountedASM
