-- Prove2me | Theorems.Thm_PoissonDepTrials_SecondOrder_delta_stein_eq
-- name    : PoissonDepTrials.SecondOrder.delta_stein_eq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T05:38:55.198098+00:00
-- url     : https://prove2.me/theorems/34ca14bb-7f33-4ccd-8209-24d307c51802
-- title:
--   (3.6), p. 537 — ΔS_λh(w) = −λ^{−1}[h(w) − 𝒫_λh − (w − λ)S_λh(w)] for w ≥ 1
-- statement:
--   Let $\lambda>0$ and let $h$ be bounded on the nonnegative integers. For every $w\ge1$,
--   $$\Delta S_\lambda h(w)=-\lambda^{-1}\bigl[h(w)-\mathscr P_\lambda h-(w-\lambda)S_\lambda h(w)\bigr].$$
--
--   The identity expresses the increment of the Stein solution through its value; together with a bound on $S_\lambda h$ it gives Lemma 3.5, and it is used again, with $b$ and $U_\lambda h$ in place of $\lambda$ and $h$, in the proof of Lemma 5.5.
--
--   **Formalization Note** $\lambda>0$ is implicit on the page (it divides by $\lambda$). $\|h\|$ is replaced by a bound $M$ on $|h|$.
-- source:
--   Chen, Poisson approximation for dependent trials, Ann. Probab. 3 (1975), p. 537, proof of Lemmas 3.4 and 3.5, (3.6)

import Mathlib
import Definitions.Def_PoissonDepTrials_SecondOrder_Setting

open MeasureTheory ProbabilityTheory Finset

namespace PoissonDepTrials.SecondOrder

/-- (3.6), p. 537: for `w ≥ 1`, `ΔS_λh(w) = −λ^{−1}[h(w) − 𝒫_λh − (w − λ) S_λh(w)]`. -/
theorem delta_stein_eq (lam : ℝ) (hlam : 0 < lam) (h : ℕ → ℝ) (M : ℝ) (hM : ∀ k, |h k| ≤ M) :
    ∀ w : ℕ, 1 ≤ w → delta (stein lam h) w =
      -lam⁻¹ * (h w - poissonExp lam h - ((w : ℝ) - lam) * stein lam h w) := by sorry

end PoissonDepTrials.SecondOrder
