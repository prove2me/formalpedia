-- Prove2me | Theorems.Thm_PoissonDepTrials_SecondOrder_stein_solution
-- name    : PoissonDepTrials.SecondOrder.stein_solution
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T05:38:46.188328+00:00
-- url     : https://prove2.me/theorems/f64da37d-778c-47d3-8d1c-a8337fceaddb
-- title:
--   (2.3)/(2.5), p. 536 — S_λh solves wf(w) − λf(w + 1) = h(w) − 𝒫_λh and equals (w − 1)! λ^{−w} Σ_{k≥w} [h(k) − 𝒫_λh]λ^k/k! for w ≥ 1
-- statement:
--   Let $\lambda>0$ and let $h$ be a bounded real function on the nonnegative integers. Let $S_\lambda h$ be given for $w\ge1$ by the first line of (2.5). Then:
--
--   1. $S_\lambda h$ solves the Stein equation (2.3): for every $w\ge0$,
--   $$wS_\lambda h(w)-\lambda S_\lambda h(w+1)=h(w)-\mathscr P_\lambda h ;$$
--   2. for every $w\ge1$ it has the tail representation (second line of (2.5))
--   $$S_\lambda h(w)=(w-1)!\,\lambda^{-w}\sum_{k=w}^\infty\bigl[h(k)-\mathscr P_\lambda h\bigr]\frac{\lambda^k}{k!}.$$
--
--   The two representations are the starting point of every bound on $S_\lambda h$: the first is used when $w\le\lambda$, the second when $w\ge\lambda$.
--
--   **Formalization Note** At $w=0$ the left side of (2.3) is $-\lambda S_\lambda h(1)$, since the value at $0$ is multiplied by $0$ (the page: "the value of $f$ at $w=0$ does not enter"). $\lambda>0$ is implicit on the page, which divides by $\lambda^w$. $\|h\|$ is replaced by a bound $M$ with $|h(k)|\le M$ for all $k$.
-- source:
--   Chen, Poisson approximation for dependent trials, Ann. Probab. 3 (1975), p. 536, §2, (2.3), (2.4), (2.5)

import Mathlib
import Definitions.Def_PoissonDepTrials_SecondOrder_Setting

open MeasureTheory ProbabilityTheory Finset

namespace PoissonDepTrials.SecondOrder

/-- (2.3)/(2.5), p. 536: for `λ > 0` and bounded `h`, `S_λh` solves the Stein equation
`w f(w) − λ f(w + 1) = h(w) − 𝒫_λh` (at every `w ≥ 0`; at `w = 0` the value `S_λh(0)` is multiplied
by `0`), and for `w ≥ 1` it also has the tail form of the second line of (2.5). -/
theorem stein_solution (lam : ℝ) (hlam : 0 < lam) (h : ℕ → ℝ) (M : ℝ) (hM : ∀ k, |h k| ≤ M) :
    (∀ w : ℕ, (w : ℝ) * stein lam h w - lam * stein lam h (w + 1) = h w - poissonExp lam h) ∧
    (∀ w : ℕ, 1 ≤ w → stein lam h w = ((w - 1).factorial : ℝ) * (lam ^ w)⁻¹ *
      ∑' k : ℕ, (h (k + w) - poissonExp lam h) * lam ^ (k + w) / ((k + w).factorial : ℝ)) := by sorry

end PoissonDepTrials.SecondOrder
