-- Prove2me | Theorems.Thm_SelfScaledIPM_FuncProx_proposition_3_5
-- name    : SelfScaledIPM.FuncProx.proposition_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:20:18.391834+00:00
-- url     : https://prove2.me/theorems/64416048-820c-4980-84d9-892df1e57556
-- title:
--   Proposition 3.5, p. 9 — |a|_b ≤ ‖a‖_b ≤ ν^{1/2}|a|_b for a ∈ E or E*, b ∈ int K or int K*
-- statement:
--   Let $K$ be a proper cone with a $\nu$-self-scaled barrier $F$. For $a\in E$ or $a\in E^*$ and for $b\in\operatorname{int}K$ or $b\in\operatorname{int}K^*$,
--   $$|a|_b\le\|a\|_b\le\nu^{1/2}|a|_b .$$
--   The four combinations of spaces are four separate statements:
--
--   1. $a\in E$, $b\in\operatorname{int}K$ (norm of $F$ at $b$, σ relative to $K$ centred at $b$);
--   2. $a\in E^*$, $b\in\operatorname{int}K$ (dual norm of $F$ at $b$, σ relative to $K^*$ centred at $-F'(b)$);
--   3. $a\in E^*$, $b\in\operatorname{int}K^*$ (norm of $F_*$ at $b$, σ relative to $K^*$ centred at $b$);
--   4. $a\in E$, $b\in\operatorname{int}K^*$ (dual norm of $F_*$ at $b$, σ relative to $K$ centred at $-F_*'(b)$).
--
--   The proposition compares the Euclidean-type local norm with the "infinity-type" norm $|\cdot|_b$ and is used repeatedly to pass between the measures $\lambda_2$ and $\lambda_\infty$.
-- source:
--   Nesterov & Todd, Primal-dual interior-point methods for self-scaled cones, SIAM J. Optim. 8 (1998) 324–364 (authors' copy, Cornell eCommons), p. 9, Proposition 3.5

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_FuncProx_Setting
import Definitions.Def_SelfScaledIPM_FuncProx_Measures

open scoped InnerProductSpace

namespace SelfScaledIPM.FuncProx

/-- **Proposition 3.5** (p. 9): `|a|_b ≤ ‖a‖_b ≤ ν^{1/2} |a|_b` for `a ∈ E` or `E*` and
`b ∈ int K` or `int K*` — the four cases as four conjuncts:
`a ∈ E, b ∈ int K`; `a ∈ E*, b ∈ int K`; `a ∈ E*, b ∈ int K*`; `a ∈ E, b ∈ int K*`. -/
theorem proposition_3_5
    {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : SelfScaledIPM.ShortStep.IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : SelfScaledIPM.ShortStep.IsSelfScaledBarrier K F ν) :
    (∀ b ∈ interior K, ∀ a : EuclideanSpace ℝ (Fin n),
      SelfScaledIPM.ShortStep.absn K b a ≤ SelfScaledIPM.ShortStep.lnorm F b a ∧ SelfScaledIPM.ShortStep.lnorm F b a ≤ Real.sqrt ν * SelfScaledIPM.ShortStep.absn K b a) ∧
    (∀ b ∈ interior K, ∀ a : EuclideanSpace ℝ (Fin n),
      SelfScaledIPM.ShortStep.absn (ConvexOptimization.dualCone K) (-gradient F b) a ≤ SelfScaledIPM.ShortStep.dnorm F b a ∧
        SelfScaledIPM.ShortStep.dnorm F b a ≤ Real.sqrt ν * SelfScaledIPM.ShortStep.absn (ConvexOptimization.dualCone K) (-gradient F b) a) ∧
    (∀ b ∈ interior (ConvexOptimization.dualCone K), ∀ a : EuclideanSpace ℝ (Fin n),
      SelfScaledIPM.ShortStep.absn (ConvexOptimization.dualCone K) b a ≤ SelfScaledIPM.ShortStep.lnorm (SelfScaledIPM.ShortStep.conj K F) b a ∧
        SelfScaledIPM.ShortStep.lnorm (SelfScaledIPM.ShortStep.conj K F) b a ≤ Real.sqrt ν * SelfScaledIPM.ShortStep.absn (ConvexOptimization.dualCone K) b a) ∧
    (∀ b ∈ interior (ConvexOptimization.dualCone K), ∀ a : EuclideanSpace ℝ (Fin n),
      SelfScaledIPM.ShortStep.absn K (-gradient (SelfScaledIPM.ShortStep.conj K F) b) a ≤ SelfScaledIPM.ShortStep.dnorm (SelfScaledIPM.ShortStep.conj K F) b a ∧
        SelfScaledIPM.ShortStep.dnorm (SelfScaledIPM.ShortStep.conj K F) b a ≤ Real.sqrt ν * SelfScaledIPM.ShortStep.absn K (-gradient (SelfScaledIPM.ShortStep.conj K F) b) a) := by sorry

end SelfScaledIPM.FuncProx
