-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_frontier_projection_count_iff
-- name    : WeierstrassEllipticZeta.frontier_projection_count_iff
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-12T22:57:23.769622+00:00
-- url     : https://prove2.me/theorems/c36dc4f6-156d-4860-afd4-167da3f474b2
-- title:
--   Subgroup bounds as point and period-class counts
-- statement:
--   Fix the elliptic-extension geometry with period lattice $\Lambda$. Let $C\ge0$, let $m,U$ be natural numbers, let $n\ge1$, and let $X$ be a finite subset of the complex numbers.
--
--   The mission's subgroup-bound conclusion is equivalent to the following numerical alternative:
--   $$ (U+1)|X|\le Cmn^2
--   \quad\text{or}\quad
--   (U+1)|X\bmod\Lambda|\le Cn^2.$$
--   The subgroup-bound conclusion asks for a subgroup $H$ and natural exponents $a,b$, with $b\le2$, such that either $a=1$ and $H$ lies in the additive-projection kernel, or $a=0$ and $H$ lies in the elliptic-projection kernel, and
--   $$ (U+1)|\phi(X)\bmod H|\le Cm^a n^b.$$
--   The constant is unchanged in both directions. From the numerical alternative, the two full projection kernels supply explicit witnesses, with exponents $(1,2)$ or $(0,2)$ respectively. No analytic or contact assumptions on $X$ are needed for this equivalence.
-- source:
--   Derived projection-count equivalence for the existing frontier https://prove2.me/theorems/b8a099fb-b5c0-4096-b2bc-437cc1193a7b. The setting is Senthil Kumar K, Algebraic independence of values of Weierstrass elliptic and zeta functions (2026), Appendix A.2 and Theorem A.2, https://doi.org/10.1017/S001309152610145X. This equivalence concerns the precise subgroup-profile conclusion already formalized in the mission; it is not a replacement for the algebraic-group multiplicity theorem in the article. It uses quotient maps, finite image cardinalities, and monotonicity of powers at Mathlib commit 0df444a360eaa60ab8c11dca51a86af692955474.

import Definitions.Def_WeierstrassEllipticZeta_InterfaceGeometry
import Mathlib.Data.Set.Card
open WeierstrassEllipticZeta TranscendenceTheory
open scoped Classical

theorem WeierstrassEllipticZeta.frontier_projection_count_iff
    (G : Frontier.Geometry) (C : ℝ) (hC : 0 ≤ C)
    (m n U : ℕ) (hn : 1 ≤ n) (X : Finset ℂ) :
    Frontier.SubgroupBound G C m n U X ↔
      ((U + 1 : ℕ) : ℝ) * X.card ≤ C * (m : ℝ) * (n : ℝ) ^ 2 ∨
      ((U + 1 : ℕ) : ℝ) * (G.L.lattice.mkQ '' (X : Set ℂ)).ncard ≤
        C * (n : ℝ) ^ 2 := by sorry
