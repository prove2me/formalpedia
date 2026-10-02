-- Prove2me | Theorems.Thm_SennottDP_Fatou_dominated_convergence
-- name    : SennottDP.Fatou.dominated_convergence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T12:16:03.741987+00:00
-- url     : https://prove2.me/theorems/6a4cbebe-8087-45c9-bdd7-3e2509a3ac90
-- title:
--   Theorem A.2.3 (Dominated Convergence Theorem) — with a convergent dominating sequence
-- statement:
--   Assume:
--
--   1. $S$ is a countable set with a probability distribution $(P_j)_{j\in S}$;
--   2. $u(j,N)$ and $w(j,N)$ are finite real functions of $j\in S$ and $N$ with $|u(j,N)|\le w(j,N)$ for all $j, N$;
--   3. the limits $\lim_{N\to\infty} u(j,N) = u(j)$ and $\lim_{N\to\infty} w(j,N) = w(j)$ exist for every $j\in S$;
--   4. $\lim_{N\to\infty}\sum_{j\in S} P_j\, w(j,N)$ exists and equals $\sum_{j\in S} P_j\, w(j) < \infty$.
--
--   Then $\lim_{N\to\infty}\sum_{j\in S} P_j u(j,N)$ exists and
--   $$\lim_{N\to\infty}\ \sum_{j\in S} P_j\, u(j,N) \;=\; \sum_{j\in S} P_j\, u(j).$$
--
--   The dominating function may itself depend on $N$, provided its expectations converge to the expectation of its limit. This gives a sufficient condition for passing a limit through an infinite summation.
--
--   **Formalization Note** The pointwise limits $u(j)$, $w(j)$ are taken in `EReal`, as the book allows limits of extended-real sequences (p. 271); the hypotheses force them to be finite wherever $P_j>0$. Sums are the weighted sum `wsum`; the sums $\sum_j P_j w(j,N)$ lie in $[0,\infty]$ and may be infinite for finitely many $N$, and the conclusion concerns only large $N$.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 276, Theorem A.2.3

import Mathlib
import Definitions.Def_SennottDP_Fatou_Basic

open Filter Topology
open scoped ENNReal

namespace SennottDP.Fatou

/-- Sennott (1999), Theorem A.2.3 (Dominated Convergence Theorem), p. 276.
(i) `S` is countable with probability distribution `(P_j)`; (ii) `u(j, N)`, `w(j, N)` are finite
with `|u| ≤ w`; (iii) `lim_N u(·, N) = u(·)` and `lim_N w(·, N) = w(·)` exist (limits in `[−∞, ∞]`);
(iv) `lim_N ∑_j P_j w(j, N)` exists and equals `∑_j P_j w(j) < ∞`. Then
`lim_N ∑_j P_j u(j, N)` exists and equals `∑_j P_j u(j)`. -/
theorem dominated_convergence {S : Type*} [Countable S] (P : S → ℝ≥0∞) (hP : ∑' j, P j = 1)
    (u w : S → ℕ → ℝ) (hdom : ∀ j N, |u j N| ≤ w j N)
    (uL wL : S → EReal)
    (hu : ∀ j, Tendsto (fun N => (u j N : EReal)) atTop (𝓝 (uL j)))
    (hw : ∀ j, Tendsto (fun N => (w j N : EReal)) atTop (𝓝 (wL j)))
    (hsum : Tendsto (fun N => wsum P (fun j => (w j N : EReal))) atTop (𝓝 (wsum P wL)))
    (hfin : wsum P wL < ⊤) :
    Tendsto (fun N => wsum P (fun j => (u j N : EReal))) atTop (𝓝 (wsum P uL)) := by sorry

end SennottDP.Fatou
