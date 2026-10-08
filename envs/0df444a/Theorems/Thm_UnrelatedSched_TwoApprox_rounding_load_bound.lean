-- Prove2me | Theorems.Thm_UnrelatedSched_TwoApprox_rounding_load_bound
-- name    : UnrelatedSched.TwoApprox.rounding_load_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T14:17:03.902752+00:00
-- url     : https://prove2.me/theorems/630ae928-e6e4-4512-8ed0-39119d15fa40
-- title:
--   §2, proof of Theorem 1, p. 5 — at most one fractional job per machine gives loads at most d_i + t
-- statement:
--   Let $P=(p_{ij})\in\mathbb N^{m\times n}$, deadlines $d_1,\dots,d_m\in\mathbb R$ and $t\ge 0$. Let $\tilde x$ be a feasible solution of (LP), and let $\sigma$ be a schedule supported on $\tilde x$ (that is, $\tilde x_{\sigma(j)j}>0$ for every job $j$) such that for each machine $i$ there is at most one job $j$ with $\sigma(j)=i$ and $\tilde x_{ij}<1$. Then for every machine $i$,
--   $$\sum_{j:\sigma(j)=i}p_{ij}\;\le\;\sum_{j\in J_i(t)}p_{ij}\tilde x_{ij}+t\;\le\; d_i+t .$$
--
--   This is the final step of the Rounding Theorem: the rounded schedule is a solution of (IP).
--
--   **Formalization Note** The paper's rounded point $\bar x$ is the 0-1 matrix of $\sigma$; "at most one job $j$ such that $\tilde x_{ij}<\bar x_{ij}=1$" is the hypothesis on $\sigma$ above. The conclusion is the outer inequality, the load bound. The paper's $t$ is a nonnegative integer; the statement takes any real $t\ge 0$.
-- source:
--   Lenstra, Shmoys, Tardos, Approximation algorithms for scheduling unrelated parallel machines, CWI Report OS-R8714 (1987), p. 5, §2, proof of Theorem 1

import Mathlib
import Definitions.Def_MatousekLP_Scheduling_Schedule
import Definitions.Def_UnrelatedSched_TwoApprox_DeadlineLP

namespace UnrelatedSched.TwoApprox

open MatousekLP.Scheduling

/-- §2, proof of Theorem 1, p. 5: a schedule supported on a feasible point of (LP) that, on each
machine, has at most one job with `x̃_ij < 1` has loads at most `d_i + t`. -/
theorem rounding_load_bound {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ) (d : Fin m → ℝ) (t : ℝ)
    (ht : 0 ≤ t) (x : Matrix (Fin m) (Fin n) ℝ) (hx : LPFeasible P d t x)
    (σ : Fin n → Fin m) (hσ : SupportedOn x σ)
    (hfrac : ∀ i (j₁ j₂ : Fin n), σ j₁ = i → σ j₂ = i → x i j₁ < 1 → x i j₂ < 1 → j₁ = j₂) :
    ∀ i, load (realTimes P) σ i ≤ d i + t := by sorry

end UnrelatedSched.TwoApprox
