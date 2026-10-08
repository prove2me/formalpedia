-- Prove2me | Theorems.Thm_SchedComplexity_Tardiness_claim_C
-- name    : SchedComplexity.Tardiness.claim_C
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T05:06:48.953561+00:00
-- url     : https://prove2.me/theorems/ee750e2d-014d-4ac6-bd34-ade2ec6816ea
-- title:
--   Theorem 4(d), claim (C) — $c_\pi<0\Rightarrow\sum w_jT_j>y$
-- statement:
--   Let $a_1,\dots,a_t$ be positive integers and $b$ an integer with $0<b<A$, where $A=\sum_{j=1}^t a_j$ and $a_*=\max_j a_j$ (the paper's standing assumption "we may assume that $0<b<A$", p. 16). Put
--
--   $$t'=\Big\lceil \tfrac12(t+1)(A-b)+\tfrac12\,t(t+1)a_*^2\Big\rceil ,$$
--
--   let $\tau$ be any integer with $\tau>2t'+A$, and consider the single-machine instance of Theorem 4(d) with $n=t+t'$ jobs: for $j\in T=\{1,\dots,t\}$, $p_j=\tau+a_j$, $w_j=\tau+a_j+1$, $d_j=t\tau+b$; for the $t'$ dummy jobs $j\notin T$, $p_j=\tau$, $w_j=\tau+1$, $d_j=t\tau+b$. Setting $a_j=0$ for $j\notin T$, every job has $p_j=\tau+a_j$ and $w_j=p_j+1$. The threshold is
--
--   $$y=\tfrac12\,t'(t'+1)\tau(\tau+1)+(t'+1)\tau(A-b)+t'.$$
--
--   For a processing order $\pi=(\pi(1),\dots,\pi(n))$ the jobs are processed without idle time from time $0$, so the job in position $j$ completes at $C_{\pi(j)}=\sum_{i\le j}p_{\pi(i)}$, and
--
--   $$c_\pi=C_{\pi(t)}-(t\tau+b).$$
--
--   If $c_\pi<0$ for a processing order $\pi$, then its schedule without idle time satisfies
--
--   $$\sum_j w_jT_j>y.$$
--
--   This is where the condition $\tau>2t'+A$ is used.
--
--   **Formalization Note** The paper prints $t'=\tfrac12(t+1)(A-b)+\tfrac12t(t+1)a_*^2$, which is a half-integer when $(t+1)(A-b)$ is odd although $t'$ counts jobs; the Lean takes its ceiling (`tPrime`), and $y$ (`yThr`, an exact natural-number division since $t'(t'+1)$ is even) is computed from the same $t'$. Jobs are `Fin (t + t')`, the items of $T$ being the indices $0,\dots,t-1$ (`aExt` is the convention $a_j=0$ for $j\notin T$). Positions are 0-based in Lean: `π i` is the paper's $\pi(i+1)$, and `posCompletion p π k` is the paper's $C_{\pi(k)}$ for the 1-based position $k$ (the total processing time of the first $k$ positions). Sums $\sum_{j>t}$ run over the 0-based positions $i\ge t$ (`tailWeighted`). $\tau$ is quantified over all naturals with $\tau>2t'+A$, as in the paper.
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), p. 20 (statement), p. 21 (proof), proof of Theorem 4(d), claim (C)

import Mathlib
import Definitions.Def_SchedComplexity_Tardiness_Construction

namespace SchedComplexity.Tardiness

/-- Claim (C) of the proof of Theorem 4(d), p. 20 (proof p. 21): if `c_π < 0`, then the schedule
without idle time of `π` has `Σ w_j T_j > y`. -/
theorem claim_C {t : ℕ} (a : Fin t → ℕ) (b τ : ℕ)
    (ha : ∀ j, 0 < a j) (hb : 0 < b) (hbA : b < bigA a)
    (hτ : 2 * tPrime a b + bigA a < τ)
    (π : Equiv.Perm (Fin (t + tPrime a b))) (hc : cPi a b τ π < 0) :
    (yThr a b τ : ℤ) < orderTWT (wtP a b τ) (wtW a b τ) (wtD a b τ) π := by sorry

end SchedComplexity.Tardiness
