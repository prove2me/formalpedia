-- Prove2me | Theorems.Thm_STOC2027BoolCSP_Approximation_proposition_4_2
-- name    : STOC2027BoolCSP.Approximation.proposition_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:53:22.270721+00:00
-- url     : https://prove2.me/theorems/2f8bb79e-632f-40fa-a44f-bb8d98746131
-- title:
--   Proposition 4.2 — Bakshi's variational bound, equation (9)
-- statement:
--   Let $R\succ0$ be an $m\times m$ correlation matrix and $X\sim N(0,R)$. With $F$ as in equation (8), the potential $\Psi_R(b)=\sum_{i=1}^mF(b_i)-\frac12b^{\mathsf T}R^{-1}b$ attains its maximum over $b\in(0,\infty)^m$, and
--   $$\log\Pr(X\ge0)\;\ge\;\max_{b\in(0,\infty)^m}\Bigl\{\sum_{i=1}^mF(b_i)-\tfrac12\,b^{\mathsf T}R^{-1}b\Bigr\}.$$
--
--   The bound turns an $m$-dimensional orthant probability into a finite-dimensional optimization. Lemma 5.1 evaluates it at a uniform test point.
--
--   **Formalization Note** "max" is stated in full: there is a $b^\ast$ with positive coordinates whose potential is at least that of every positive $b$, and $\log\Pr(X\ge0)$ is at least $\Psi_R(b^\ast)$.
--
--   Differences from the source:
--
--   - encoding: log Pr(X ≥ 0) ≥ max over b ∈ (0,∞)^m → ∃ b* > 0 maximizing the potential over all positive b, and potential(b*) ≤ log Pr(X ≥ 0); reason: this is the meaning of the attained maximum
--   - encoding: a(b) the unique positive centering tilt → Hilbert ε-choice of a positive root of the centering integral; reason: the root exists and is unique for b > 0 (Section 4), so the choice is the paper's a(b)
-- source:
--   Zhijie Zheng, Yucong He, Chengzhi Xie, Approximation and Even Arity Hardness for Boolean Constraint Satisfaction, STOC 2027 submission #40 (October 2026), printed p. 7 (PDF 10), Proposition 4.2, equation (9)

import Mathlib
import Definitions.Def_STOC2027BoolCSP_Approximation_Gaussian

namespace STOC2027BoolCSP.Approximation

/-- Proposition 4.2 (Bakshi's variational bound), equation (9), printed p. 7: the potential
`Σ_i F(b_i) − ½ bᵀR⁻¹b` attains its maximum over `b ∈ (0,∞)^m`, and that maximum is at most
`log Pr(X ≥ 0)`. -/
theorem proposition_4_2 (m : ℕ) (R : Matrix (Fin m) (Fin m) ℝ) (hR_pd : R.PosDef)
    (hR_diag : ∀ i, R i i = 1) :
    ∃ bstar : Fin m → ℝ, (∀ i, 0 < bstar i) ∧
      (∀ b : Fin m → ℝ, (∀ i, 0 < b i) → potential R b ≤ potential R bstar) ∧
      potential R bstar ≤ Real.log (orthantProb R) := by sorry

end STOC2027BoolCSP.Approximation
