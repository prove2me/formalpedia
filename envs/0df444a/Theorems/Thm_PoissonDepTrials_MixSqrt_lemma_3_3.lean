-- Prove2me | Theorems.Thm_PoissonDepTrials_MixSqrt_lemma_3_3
-- name    : PoissonDepTrials.MixSqrt.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:37:50.145568+00:00
-- url     : https://prove2.me/theorems/3ed821b6-9038-433e-bbe9-c9136635bc3d
-- title:
--   Lemma 3.3, p. 537 — ‖S_λh‖ ≤ 4‖h‖ min(λ^{−1/2}, 1)
-- statement:
--   Let $\lambda>0$ and let $h$ be a real function on the nonnegative integers with $|h(k)|\le M$ for all $k$. Then the Stein solution (2.5) satisfies, for every $w\ge1$,
--   $$|S_\lambda h(w)|\le 4M\min(\lambda^{-1/2},1).$$
--   Equivalently, $\|S_\lambda h\|\le4\|h\|\min(\lambda^{-1/2},1)$, the sup norm of $S_\lambda h$ being taken over its domain $w\ge1$.
--
--   This is the bound used on the middle error term of (2.6), through Lemma 4.6.
--
--   **Formalization Note** The sup norm $\|h\|$ is replaced by an arbitrary bound $M$ on $|h|$, which is equivalent since $\|h\|$ is the least such bound. The hypothesis $\lambda>0$ is implicit on the page. $\lambda^{-1/2}$ is written $1/\sqrt\lambda$.
-- source:
--   Chen, Poisson approximation for dependent trials, Ann. Probab. 3 (1975), p. 537, Lemma 3.3, (3.3)

import Mathlib
import Definitions.Def_PoissonDepTrials_MixSqrt_Setting

open MeasureTheory ProbabilityTheory

namespace PoissonDepTrials.MixSqrt

/-- Chen (1975), Lemma 3.3, p. 537, (3.3): `‖S_λh‖ ≤ 4‖h‖ min(λ^{−1/2}, 1)`, with `‖h‖` given
as any bound `M` on `|h|` and `‖S_λh‖` the supremum over `w ≥ 1`. -/
theorem lemma_3_3 (lam : ℝ) (hlam : 0 < lam) (h : ℕ → ℝ) (M : ℝ) (hM : ∀ k, |h k| ≤ M) :
    ∀ w : ℕ, 1 ≤ w → |stein lam h w| ≤ 4 * M * min (1 / Real.sqrt lam) 1 := by sorry

end PoissonDepTrials.MixSqrt
