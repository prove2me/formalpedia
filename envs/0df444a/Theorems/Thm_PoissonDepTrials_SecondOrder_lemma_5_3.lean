-- Prove2me | Theorems.Thm_PoissonDepTrials_SecondOrder_lemma_5_3
-- name    : PoissonDepTrials.SecondOrder.lemma_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:52:23.734144+00:00
-- url     : https://prove2.me/theorems/7abb3a07-85be-4abb-805b-593f4f9faec4
-- title:
--   Lemma 5.3, p. 543 — 𝒫_b|L^mU_λh| ≤ 2λ^{−1}‖h‖[1 + 2|m + 1 + b − λ| + 2b^½ min(λ^{−½}, 1)]
-- statement:
--   Let $\lambda>0$, $b>0$, $|h(k)|\le M$ for all $k$, and $m\ge0$ an integer. With $L^mU_\lambda h(w)=U_\lambda h(w+m)$,
--   $$\mathscr P_b\bigl|L^mU_\lambda h\bigr|\le2\lambda^{-1}M\Bigl[1+2|m+1+b-\lambda|+2b^{1/2}\min(\lambda^{-1/2},1)\Bigr].$$
--
--   Equivalently, for $Y$ Poisson with mean $b$, $E|U_\lambda h(Y+m)|$ is of order $\lambda^{-1}$ when $b$ and $\lambda$ are close; this controls the terms produced by Lemma 5.2 in the proof of Theorem 5.1.
--
--   **Formalization Note** The integer $m$ is a shift, unrelated to the dependence range of §2. $b>0$ is the standing range of the parameter in §5 (Lemmas 5.1, 5.2); $\lambda>0$ is implicit. $\|h\|$ is replaced by a bound $M$.
-- source:
--   Chen, Poisson approximation for dependent trials, Ann. Probab. 3 (1975), p. 543, Lemma 5.3, (5.3)

import Mathlib
import Definitions.Def_PoissonDepTrials_SecondOrder_Setting

open MeasureTheory ProbabilityTheory Finset

namespace PoissonDepTrials.SecondOrder

/-- Lemma 5.3, (5.3), p. 543: for `m = 0, 1, 2, …`,
`𝒫_b|L^m U_λh| ≤ 2λ^{−1}‖h‖[1 + 2|m + 1 + b − λ| + 2b^{1/2} min(λ^{−1/2}, 1)]`,
with `L^m U_λh(w) = U_λh(w + m)`. -/
theorem lemma_5_3 (lam : ℝ) (hlam : 0 < lam) (b : ℝ) (hb : 0 < b) (h : ℕ → ℝ) (M : ℝ)
    (hM : ∀ k, |h k| ≤ M) (m : ℕ) :
    poissonExp b (fun w => |stU lam h (w + m)|) ≤
      2 * lam⁻¹ * M * (1 + 2 * |(m : ℝ) + 1 + b - lam| + 2 * Real.sqrt b * min (1 / Real.sqrt lam) 1) := by sorry

end PoissonDepTrials.SecondOrder
