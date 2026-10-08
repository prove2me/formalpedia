-- Prove2me | Theorems.Thm_TroppMatrixConcentration_ch8_perspective_convex
-- name    : TroppMatrixConcentration.ch8_perspective_convex
-- status  : Proved
-- author  : @tc
-- created : 2026-10-07T13:53:10.64345+00:00
-- url     : https://prove2.me/theorems/03d4b4d4-1438-42c0-8700-a23753d76cde
-- title:
--   Theorem 8.6.2 — Matrix perspective is jointly operator convex
-- statement:
--   Let $f$ be operator convex on $(0,\infty)$ and let $A_1,A_2,H_1,H_2$ be positive-definite complex matrices of the same positive dimension. For every $0\le t\le1$,
--   $$\Psi_f(tA_1+(1-t)A_2;\,tH_1+(1-t)H_2)\preceq t\Psi_f(A_1;H_1)+(1-t)\Psi_f(A_2;H_2).$$
--   Here $\Psi_f(A;H)=A^{1/2}f(A^{-1/2}HA^{-1/2})A^{1/2}$. No pair of the matrices is required to commute. This supplies the bivariate operator-convexity result used in the entropy analysis.
-- source:
--   Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Theorem 8.6.2, printed pp. 134–135.

import Definitions.Def_TroppMatrixConcentration_ch8_entropy

open scoped Matrix.Norms.L2Operator ComplexOrder

namespace TroppMatrixConcentration

theorem ch8_perspective_convex {d : ℕ} [NeZero d]
    (f : ℝ → ℝ) (hf : ch8_operatorConvexOn (Set.Ioi 0) f)
    (A₁ A₂ H₁ H₂ : Matrix (Fin d) (Fin d) ℂ)
    (hA₁ : A₁.PosDef) (hA₂ : A₂.PosDef) (hH₁ : H₁.PosDef) (hH₂ : H₂.PosDef)
    (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    loewnerLE
      (ch8_perspective f (t • A₁ + (1 - t) • A₂) (t • H₁ + (1 - t) • H₂))
      (t • ch8_perspective f A₁ H₁ + (1 - t) • ch8_perspective f A₂ H₂) := by sorry

end TroppMatrixConcentration
