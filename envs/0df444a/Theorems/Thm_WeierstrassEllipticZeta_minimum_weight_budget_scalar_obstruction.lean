-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_minimum_weight_budget_scalar_obstruction
-- name    : WeierstrassEllipticZeta.minimum_weight_budget_scalar_obstruction
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-23T03:11:23.473003+00:00
-- url     : https://prove2.me/theorems/a2d64257-ed70-401b-9497-4f3814406b13
-- title:
--   Point and period multiplicity alternatives from a minimum-weight section budget
-- statement:
--   Let L be a period pair with lattice Λ, let η be any integer-linear map from Λ to the complex numbers, and fix a finite set X, coordinate functions S, polynomial Q, positive integers m,n, nonnegative integers U,E, a set K and a finite list Z. Let W be the existing minimum anchor weight for these inputs, and let V be the first-chart section space of bidegree (m,n).
--
--   Suppose C is nonnegative, E is at least U+1, and W E ≤ C dim(V). Then at least one of the following holds:
--
--   $$ (U+1)|X|\le 10 C m n^2,\qquad
--      (U+1)|X\bmod\Lambda|\le 5 C n^2. $$
--
--   This is a conditional numerical implication. It requires no analytic hypotheses on S or Q, and no exactness hypothesis on Z, because the minimum-weight lower bound is unconditional. For A.1 the necessary analytic inputs establish the contact bound, and the existing Open geometric theorem is still needed to supply the budget.
-- source:
--   Derived numerical bridge for Senthil Kumar K, Appendix A.2, https://www.cambridge.org/core/journals/proceedings-of-the-edinburgh-mathematical-society/article/algebraic-independence-of-values-of-weierstrass-elliptic-and-zeta-functions/E91A8EEEB1F63536D95D1DE7D7DD47E2#app1. This is a consequence of previously proved optimizer and section-dimension bounds, not a quoted paper formula. The inequalities min(N,(m+1)*q)<=W, U+1<=E and dim(V)<=5*(m+1)*n^2 turn the assumed geometric budget W*E<=C*dim(V) into either (U+1)*N<=10*C*m*n^2 or (U+1)*q<=5*C*n^2. The geometric budget is still Open.

import Definitions.Def_WeierstrassEllipticZeta_OptimalAnchorWeight
import Definitions.Def_WeierstrassEllipticZeta_FirstChartSections
open WeierstrassEllipticZeta
open scoped Classical

theorem WeierstrassEllipticZeta.minimum_weight_budget_scalar_obstruction
    (L : PeriodPair) (η : L.lattice →ₗ[ℤ] ℂ)
    (X : Finset ℂ) (S : Fin 5 → ℂ → ℂ) (Q : MvPolynomial (Fin 7) ℂ)
    (m n U E : ℕ) (K : Set ℂ) (Z : Finset ℂ) (C : ℝ)
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hC : 0 ≤ C)
    (hcontact : U + 1 ≤ E)
    (hbudget : (((minimumAnchorWeight L.lattice η X S Q m n K Z * E : ℕ) : ℝ)
      ≤ C * (Module.finrank ℂ (firstChartSectionSpace L m n) : ℝ))) :
    ((U + 1 : ℕ) : ℝ) * (X.card : ℝ) ≤ (10 * C) * (m : ℝ) * (n : ℝ) ^ 2 ∨
    ((U + 1 : ℕ) : ℝ) * ((X.image L.lattice.mkQ).card : ℝ) ≤
      (5 * C) * (n : ℝ) ^ 2 := by sorry
