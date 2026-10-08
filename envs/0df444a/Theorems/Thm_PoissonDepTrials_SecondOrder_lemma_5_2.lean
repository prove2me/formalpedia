-- Prove2me | Theorems.Thm_PoissonDepTrials_SecondOrder_lemma_5_2
-- name    : PoissonDepTrials.SecondOrder.lemma_5_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T05:51:59.261917+00:00
-- url     : https://prove2.me/theorems/1aceb6c1-69fd-4b89-9f97-52def56d088d
-- title:
--   Lemma 5.2, p. 543 — |𝒫_λf − 𝒫_bf| ≤ (λ − b)(𝒫_λ|Lf| + 𝒫_b|f|) for λ ≥ b > 0
-- statement:
--   Let $\lambda\ge b>0$ and let $f$ be a bounded real function on the nonnegative integers, with $Lf(w)=f(w+1)$. Then
--   $$\bigl|\mathscr P_\lambda f-\mathscr P_bf\bigr|\le(\lambda-b)\bigl(\mathscr P_\lambda|Lf|+\mathscr P_b|f|\bigr).$$
--
--   The lemma compares Poisson expectations at two parameters; in the proof of Theorem 5.1 it is applied with $b=\lambda^{(i)}=\lambda-p_i$ to replace $\mathscr P_{\lambda^{(i)}}U_\lambda h$ by $\mathscr P_\lambda U_\lambda h$.
--
--   **Formalization Note** The page states the lemma for arbitrary $f$; it is applied only to bounded $f$, and boundedness ($|f(k)|\le M$) is added so that the Poisson expectations are genuine (finite) sums.
-- source:
--   Chen, Poisson approximation for dependent trials, Ann. Probab. 3 (1975), p. 543, Lemma 5.2, (5.2)

import Mathlib
import Definitions.Def_PoissonDepTrials_SecondOrder_Setting

open MeasureTheory ProbabilityTheory Finset

namespace PoissonDepTrials.SecondOrder

/-- Lemma 5.2, (5.2), p. 543: for `λ ≥ b > 0` and bounded `f`,
`|𝒫_λf − 𝒫_bf| ≤ (λ − b)(𝒫_λ|Lf| + 𝒫_b|f|)`. -/
theorem lemma_5_2 (lam b : ℝ) (hb : 0 < b) (hbl : b ≤ lam) (f : ℕ → ℝ) (M : ℝ)
    (hM : ∀ k, |f k| ≤ M) :
    |poissonExp lam f - poissonExp b f| ≤
      (lam - b) * (poissonExp lam (fun w => |shiftL f w|) + poissonExp b (fun w => |f w|)) := by sorry

end PoissonDepTrials.SecondOrder
