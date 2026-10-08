-- Prove2me | Theorems.Thm_UncertainPricing_Superrep_proposition_2_13
-- name    : UncertainPricing.Superrep.proposition_2_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:49:38.439004+00:00
-- url     : https://prove2.me/theorems/b811485f-ded9-4afa-ac4a-8b8282437b5c
-- title:
--   Proposition 2.13, p. 9 — Λ((B_t − B_s)^{2n}) ≤ C_{2n} μ̄([s,t])^n
-- statement:
--   Let $\mathbf P$ be a set of martingale measures on $\Omega$ satisfying $H(\bar\mu)$ and let $\Lambda$ be the superreplication price. For any integer $n\ge1$ there is a constant $C_{2n}>0$ such that, for all $0\le s\le t\le T$,
--   $$\Lambda\big((B_t-B_s)^{2n}\big)\le C_{2n}\,\bar\mu([s,t])^n.$$
--
--   It is the uniform moment estimate that, combined with the dominance $E_Q\le\Lambda$, yields the continuity of $\tilde B$ under every $Q\in\mathcal Q$ (display (7)).
--
--   **Formalization Note.** $\Lambda$ takes values in $[-\infty,\infty]$; the right-hand side is a real number cast to `EReal`. $\bar\mu([s,t])=\bar\mu_t-\bar\mu_s$ since $\bar\mu$ is continuous, and $s\le t$ is assumed, as the interval $[s,t]$ presupposes.
-- source:
--   Denis & Martini, arXiv:math/0607111v1, Proposition 2.13, p. 9

import Mathlib
import Definitions.Def_UncertainPricing_Superrep_Setting

namespace UncertainPricing.Superrep

open MeasureTheory Filter Topology BoundedContinuousFunction

theorem proposition_2_13 (T : ℝ) (hT : 0 < T) (μU : StieltjesFunction ℝ) (hμU : IsDistFn T μU)
    (Ps : Set (Measure (Ω T))) (hPs : ∀ P ∈ Ps, IsMartingaleMeasure P ∧ HypU μU P)
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ s t : Set.Icc (0 : ℝ) T, s ≤ t →
      Lam Ps μU (fun ω => (B t ω - B s ω) ^ (2 * n)) ≤
        ((C * (μU t - μU s) ^ n : ℝ) : EReal) := by sorry

end UncertainPricing.Superrep
