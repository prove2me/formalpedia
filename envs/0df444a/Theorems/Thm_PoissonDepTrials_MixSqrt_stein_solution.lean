-- Prove2me | Theorems.Thm_PoissonDepTrials_MixSqrt_stein_solution
-- name    : PoissonDepTrials.MixSqrt.stein_solution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:37:38.735899+00:00
-- url     : https://prove2.me/theorems/729605bb-d00a-4a6f-a2f0-d9a1475532b5
-- title:
--   (2.3)–(2.5), p. 536 — S_λh solves wf(w) − λf(w + 1) = h(w) − 𝒫_λh and has the tail form
-- statement:
--   Let $\lambda>0$ and let $h$ be a bounded real function on the nonnegative integers, with Poisson expectation $\mathcal P_\lambda h=e^{-\lambda}\sum_{k\ge0}h(k)\lambda^k/k!$. Let
--   $$S_\lambda h(w)=-(w-1)!\,\lambda^{-w}\sum_{k=0}^{w-1}\bigl[h(k)-\mathcal P_\lambda h\bigr]\frac{\lambda^k}{k!}\qquad(w\ge1),$$
--   and $S_\lambda h(0)=0$. Then:
--
--   1. $S_\lambda h$ solves the **Stein equation** (2.3): for every $w\ge0$,
--   $$wS_\lambda h(w)-\lambda S_\lambda h(w+1)=h(w)-\mathcal P_\lambda h ;$$
--   2. for every $w\ge1$ it has the tail representation (second line of (2.5))
--   $$S_\lambda h(w)=(w-1)!\,\lambda^{-w}\sum_{k=w}^\infty\bigl[h(k)-\mathcal P_\lambda h\bigr]\frac{\lambda^k}{k!}.$$
--
--   At $w=0$ the equation involves only $S_\lambda h(1)$, which is why the value of $f$ at $0$ plays no role. Substituting $S_\lambda h$ into the basic identity (2.2) gives the error representation (2.6); the two forms of $S_\lambda h$ are what Lemmas 3.1–3.3 bound in the regimes $\lambda\ge w$ and $\lambda\le w$.
--
--   **Formalization Note** The hypothesis $\lambda>0$ is implicit on the page, where $(2.5)$ divides by $\lambda^w$. Boundedness of $h$ is given as $|h|\le M$ for some $M$.
-- source:
--   Chen, Poisson approximation for dependent trials, Ann. Probab. 3 (1975), p. 536, §2, (2.3), (2.4), (2.5)

import Mathlib
import Definitions.Def_PoissonDepTrials_MixSqrt_Setting

open MeasureTheory ProbabilityTheory

namespace PoissonDepTrials.MixSqrt

/-- Chen (1975), §2, p. 536, (2.3)–(2.5). For `λ > 0` and bounded `h`, the function `S_λh` of
(2.5) (first line) solves the Stein equation `wf(w) − λf(w + 1) = h(w) − 𝒫_λh` for every `w ≥ 0`,
and for `w ≥ 1` it also has the tail form
`S_λh(w) = (w − 1)! λ^{−w} Σ_{k=w}^∞ [h(k) − 𝒫_λh] λ^k / k!` (second line of (2.5)). -/
theorem stein_solution (lam : ℝ) (hlam : 0 < lam) (h : ℕ → ℝ) (M : ℝ)
    (hM : ∀ k, |h k| ≤ M) :
    (∀ w : ℕ, (w : ℝ) * stein lam h w - lam * stein lam h (w + 1) = h w - poissonExp lam h) ∧
    (∀ w : ℕ, 1 ≤ w → stein lam h w = ((w - 1).factorial : ℝ) * (lam ^ w)⁻¹ *
      ∑' k : ℕ, (h (k + w) - poissonExp lam h) * lam ^ (k + w) / ((k + w).factorial : ℝ)) := by sorry

end PoissonDepTrials.MixSqrt
