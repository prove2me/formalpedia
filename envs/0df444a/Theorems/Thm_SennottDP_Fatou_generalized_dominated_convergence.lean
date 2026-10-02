-- Prove2me | Theorems.Thm_SennottDP_Fatou_generalized_dominated_convergence
-- name    : SennottDP.Fatou.generalized_dominated_convergence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T12:38:43.71284+00:00
-- url     : https://prove2.me/theorems/5f6d4091-b6b0-4fe9-aedb-9a30f105ca8c
-- title:
--   Theorem A.2.6 (Generalized Dominated Convergence Theorem) — limits of sums under approximating distributions
-- statement:
--   Assume hypotheses (i)–(iii) of Proposition A.2.5: $S$ is a countable set with a probability distribution $(P_j)_{j\in S}$; $(S_N)$ is an increasing sequence of subsets of $S$ with $\bigcup_N S_N = S$; for each $N$, $(P_j(N))_{j\in S_N}$ is a probability distribution on $S_N$, and $\lim_{N\to\infty}P_j(N) = P_j$ for every $j\in S$. Assume further:
--
--   4. $u(j,N)$ and $w(j,N)$ are finite real functions of $j\in S_N$ and $N$ with $|u(j,N)|\le w(j,N)$;
--   5. the limits $\lim_{N\to\infty}u(j,N) = u(j)$ and $\lim_{N\to\infty}w(j,N) = w(j)$ exist for every $j\in S$;
--   6. $\lim_{N\to\infty}\sum_{j\in S_N} P_j(N)\, w(j,N)$ exists and equals $\sum_{j\in S}P_j\, w(j) < \infty$.
--
--   Then $\lim_{N\to\infty}\sum_{j\in S_N} P_j(N)u(j,N)$ exists and
--   $$\lim_{N\to\infty}\ \sum_{j\in S_N} P_j(N)\, u(j,N) \;=\; \sum_{j\in S} P_j\, u(j).$$
--
--   This is the dominated convergence theorem for a sequence of distributions converging pointwise on an increasing sequence of supports. It is the result the approximating-sequence method uses to show that expected costs in the approximating models converge to those of the original model.
--
--   **Formalization Note** Hypotheses (i)–(iii) are the structure `ApproxDist P SN Q` with `Q N j` $=P_j(N)$. $u$ and $w$ are real valued on all of $S$, but $|u|\le w$ is required only for $j\in S_N$, and values off $S_N$ never enter the sums. The pointwise limits $u(j)$, $w(j)$ are taken in `EReal`, as the book allows limits of extended-real sequences (p. 271). All sums are the weighted sum `wsum`; the sums in hypothesis 6 lie in $[0,\infty]$ and may be infinite for finitely many $N$, and the conclusion concerns only large $N$.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 278, Theorem A.2.6

import Mathlib
import Definitions.Def_SennottDP_Fatou_Basic

open Filter Topology
open scoped ENNReal

namespace SennottDP.Fatou

/-- Sennott (1999), Theorem A.2.6 (Generalized Dominated Convergence Theorem), p. 278.
(i)–(iii) of Proposition A.2.5 are `ApproxDist P SN Q` (`Q N j = P_j(N)`); (iv) `u(j, N)`, `w(j, N)`
are finite functions of `j ∈ S_N` and `N` with `|u| ≤ w`; (v) `lim_N u(·, N) = u(·)` and
`lim_N w(·, N) = w(·)` exist (limits in `[−∞, ∞]`); (vi) `lim_N ∑_{j ∈ S_N} P_j(N) w(j, N)` exists and
equals `∑_{j ∈ S} P_j w(j) < ∞`. Then `lim_N ∑_{j ∈ S_N} P_j(N) u(j, N)` exists and equals
`∑_{j ∈ S} P_j u(j)`. -/
theorem generalized_dominated_convergence {S : Type*} [Countable S] {P : S → ℝ≥0∞}
    {SN : ℕ → Set S} {Q : ℕ → S → ℝ≥0∞} (hA : ApproxDist P SN Q)
    (u w : S → ℕ → ℝ) (hdom : ∀ N, ∀ j ∈ SN N, |u j N| ≤ w j N)
    (uL wL : S → EReal)
    (hu : ∀ j, Tendsto (fun N => (u j N : EReal)) atTop (𝓝 (uL j)))
    (hw : ∀ j, Tendsto (fun N => (w j N : EReal)) atTop (𝓝 (wL j)))
    (hsum : Tendsto (fun N => wsum ((SN N).indicator (Q N)) (fun j => (w j N : EReal))) atTop
      (𝓝 (wsum P wL)))
    (hfin : wsum P wL < ⊤) :
    Tendsto (fun N => wsum ((SN N).indicator (Q N)) (fun j => (u j N : EReal))) atTop
      (𝓝 (wsum P uL)) := by sorry

end SennottDP.Fatou
