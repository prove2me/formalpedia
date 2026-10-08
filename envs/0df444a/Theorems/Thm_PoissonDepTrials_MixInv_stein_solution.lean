-- Prove2me | Theorems.Thm_PoissonDepTrials_MixInv_stein_solution
-- name    : PoissonDepTrials.MixInv.stein_solution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:39:37.664392+00:00
-- url     : https://prove2.me/theorems/19a5034b-b6ab-4e7e-b1b1-8d7cc02bac35
-- title:
--   (2.3)/(2.5), p. 536 — S_λh solves wf(w) − λf(w+1) = h(w) − 𝒫_λh, and its tail form
-- statement:
--   Let $\lambda>0$, let $h$ be a bounded real function on the nonnegative integers, and let $S_\lambda h$ be given by the first equation of (2.5). Then
--
--   1. for every $w\ge0$,
--   $$wS_\lambda h(w)-\lambda S_\lambda h(w+1)=h(w)-\mathcal P_\lambda h,$$
--   which is Stein's equation (2.3) (at $w=0$ the left side is $-\lambda S_\lambda h(1)$, so the value at $0$ plays no role);
--   2. for every $w\ge1$,
--   $$S_\lambda h(w)=(w-1)!\,\lambda^{-w}\sum_{k=w}^\infty\bigl[h(k)-\mathcal P_\lambda h\bigr]\frac{\lambda^k}{k!}.$$
--
--   The second form is what the bounds of §3 for $\lambda\le w$ use.
--
--   **Formalization Note** $\|h\|$ is replaced by a bound $M$ with $|h(k)|\le M$; $\lambda>0$ is needed for $\lambda^{-w}$ and is stated.
-- source:
--   Chen, Poisson approximation for dependent trials, Ann. Probab. 3 (1975), p. 536, (2.3), (2.4), (2.5)

import Mathlib
import Definitions.Def_PoissonDepTrials_MixInv_Setting

open MeasureTheory ProbabilityTheory

namespace PoissonDepTrials.MixInv

theorem stein_solution (lam : ℝ) (hlam : 0 < lam) (h : ℕ → ℝ) (M : ℝ)
    (hM : ∀ k, |h k| ≤ M) :
    (∀ w : ℕ, (w : ℝ) * stein lam h w - lam * stein lam h (w + 1) = h w - poissonExp lam h) ∧
    (∀ w : ℕ, 1 ≤ w → stein lam h w = ((w - 1).factorial : ℝ) * (lam ^ w)⁻¹ *
      ∑' k : ℕ, (h (k + w) - poissonExp lam h) * lam ^ (k + w) / ((k + w).factorial : ℝ)) := by sorry

end PoissonDepTrials.MixInv
