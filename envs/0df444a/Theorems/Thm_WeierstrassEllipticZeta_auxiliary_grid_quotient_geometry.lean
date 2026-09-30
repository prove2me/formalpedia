-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_auxiliary_grid_quotient_geometry
-- name    : WeierstrassEllipticZeta.auxiliary_grid_quotient_geometry
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-08T14:41:46.336848+00:00
-- url     : https://prove2.me/theorems/b89cf2d4-cd45-49a5-99e5-c30e46ea9de3
-- title:
--   Auxiliary-grid quotient counts and triple sums
-- statement:
--   Let $L$ be a complex period pair with lattice $\Lambda$, and let $\omega,u_1,u_2\in\mathbb C$ satisfy the regular auxiliary-grid hypotheses. In particular the integer map
--
--   $$J(a,b,c)=au_1+bu_2+c\omega$$
--
--   is injective, and two integer grid points are congruent modulo $\Lambda$ exactly when their first two coordinates agree. For positive integers $A_0,A_1,A_2$ put
--
--   $$\Gamma(A_0,A_1,A_2)=\{J(a,b,c):0\le a<A_0,\ 0\le b<A_1,\ 0\le c<A_2\},$$
--
--   where all three indices are integers. Let $\pi:\mathbb C\to\mathbb C/\Lambda$ be the additive quotient map. Then
--
--   $$\begin{aligned}
--   0&\in\Gamma(A_0,A_1,A_2),\\
--   \Gamma(A_0,A_1,A_2)+\Gamma(A_0,A_1,A_2)+\Gamma(A_0,A_1,A_2)
--   &\subseteq\Gamma(3A_0,3A_1,3A_2),\\
--   |\Gamma(A_0,A_1,A_2)|&=A_0A_1A_2,\\
--   |\pi(\Gamma(A_0,A_1,A_2))|&=A_0A_1.
--   \end{aligned}$$
--
--   Here sums of finite sets mean sets of sums of their elements. The quotient count is exact: each residue class is represented by a unique pair $(a,b)$, while changing $c$ leaves its class unchanged. For the grid $\Gamma(s,s,q)$ the two counts are therefore $s^2q$ and $s^2$. No analytic or algebraic-group zero estimate is assumed or concluded.
-- source:
--   Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix (A.10)-(A.11) and the proof of Proposition A.1, https://doi.org/10.1017/S001309152610145X. This derived rank-one-intersection grid lemma makes the finite-set and lattice-quotient counts exact under the existing regular grid data, and proves the triple-sum inclusion used to pass from X(3) to the enlarged grid. It contains no geometric multiplicity estimate.

import Definitions.Def_WeierstrassEllipticZeta_AuxiliaryGrids
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Data.Set.Card

open WeierstrassEllipticZeta
open scoped Pointwise

theorem WeierstrassEllipticZeta.auxiliary_grid_quotient_geometry
    (L : PeriodPair) (ω u₁ u₂ : ℂ)
    (h_grid : RegularAuxiliaryGridData L ω u₁ u₂)
    (A : Fin 3 → ℕ) (hA : ∀ i, 1 ≤ A i) :
    0 ∈ auxiliaryGrid u₁ u₂ ω A ∧
    (auxiliaryGrid u₁ u₂ ω A + auxiliaryGrid u₁ u₂ ω A +
      auxiliaryGrid u₁ u₂ ω A ⊆ auxiliaryGrid u₁ u₂ ω (fun i => 3 * A i)) ∧
    (auxiliaryGrid u₁ u₂ ω A).card = A 0 * A 1 * A 2 ∧
    (L.lattice.mkQ '' (auxiliaryGrid u₁ u₂ ω A : Set ℂ)).ncard = A 0 * A 1 := by sorry
