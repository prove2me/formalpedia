-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_coordinate_stable_quotient_bound
-- name    : WeierstrassEllipticZeta.coordinate_stable_quotient_bound
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-13T01:21:08.860193+00:00
-- url     : https://prove2.me/theorems/c83f308a-0422-4fdd-981f-dd0ad12214c3
-- title:
--   A quotient dimension bound from a coordinate-stable span
-- statement:
--   Let $K$ be a field, let $\sigma$ be any set of variables, and let $J$ be an ideal of the polynomial ring $K[\sigma]$. Write $A=K[\sigma]/J$ and let $v_0,\ldots,v_{d-1}$ be a family of elements of $A$. Let $V$ be their $K$-linear span, and write $\overline X_i$ for the image of coordinate $X_i$ in $A$.
--
--   Suppose $1\in V$ and $\overline X_i v_j\in V$ for every variable $i\in\sigma$ and every $0\le j<d$. Then $V=A$, the quotient $A$ is finite-dimensional over $K$, and
--   $$\dim_K A\le d.$$
--
--   The family need not be linearly independent, the number of variables need not be finite, and the conclusion includes the zero quotient and the case $d=0$.
-- source:
--   Derived coordinate-stability certificate for the frontier https://prove2.me/theorems/83774ea5-37c2-4247-b493-b05435c24fd5. The mission setting is Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2 and Theorem A.2, https://doi.org/10.1017/S001309152610145X. The supporting algebraic criterion is proved by polynomial and span induction using Mathlib commit 0df444a360eaa60ab8c11dca51a86af692955474. The geometric construction with a uniform generator-count bound remains open.

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Constructions

noncomputable section

theorem WeierstrassEllipticZeta.coordinate_stable_quotient_bound
    (K σ : Type*) [Field K] (J : Ideal (MvPolynomial σ K))
    (d : ℕ) (v : Fin d → MvPolynomial σ K ⧸ J)
    (hone : (1 : MvPolynomial σ K ⧸ J) ∈ Submodule.span K (Set.range v))
    (hmul : ∀ i : σ, ∀ j : Fin d,
      Ideal.Quotient.mk J (MvPolynomial.X i) * v j ∈ Submodule.span K (Set.range v)) :
    Submodule.span K (Set.range v) = ⊤ ∧
      FiniteDimensional K (MvPolynomial σ K ⧸ J) ∧
      Module.finrank K (MvPolynomial σ K ⧸ J) ≤ d := by sorry
