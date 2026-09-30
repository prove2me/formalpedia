-- Prove2me | Theorems.Thm_TranscendenceTheory_bounded_bivariate_relation_basis
-- name    : TranscendenceTheory.bounded_bivariate_relation_basis
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-14T16:18:42.467687+00:00
-- url     : https://prove2.me/theorems/e8bae1e2-dc29-4015-9529-d68cc845d4e6
-- title:
--   A finite basis for all bounded bivariate polynomial relations
-- statement:
--   Let $K$ be a field, let $A$ be a commutative $K$-algebra, and fix $x,y\in A$ and nonnegative integers $b,s$. The bivariate polynomial relations
--   $$W_{b,s}(x,y)=\{P\in K[X][Y]:\deg_Y P\le s,\ \deg_X P_i\le b\text{ for every coefficient }P_i,\ P(x,y)=0\}$$
--   have a $K$-basis consisting of at most
--   $$k\le(b+1)(s+1)$$
--   polynomials. In particular, there are linearly independent polynomials $H_0,\ldots,H_{k-1}$ whose span is exactly this relation space. The algebra $A$ need not be finite-dimensional or reduced. Degree bounds use natural degree, assigning degree zero to the zero polynomial; the zero relation space is represented by an empty basis.
-- source:
--   Derived bounded relation-space step for https://prove2.me/theorems/08ae25ab-c63e-48d2-ab17-5189a85148d9. Mission context: Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2, Theorem A.3 and Proposition A.1; https://doi.org/10.1017/S001309152610145X. This basis construction is a derived algebraic tool, not a claim to complete the paper zero estimate. Primary Lean sources: Mathlib Algebra/Polynomial/AlgebraMap.lean, Algebra/Polynomial/Degree/Defs.lean, LinearAlgebra/FiniteDimensional/Basic.lean, LinearAlgebra/Dimension/Free.lean, and LinearAlgebra/Span/Basic.lean, revision 0df444a360eaa60ab8c11dca51a86af692955474. The kernel of bounded bivariate evaluation has a basis no larger than the coefficient rectangle. It assembles individual root-avoiding witnesses into a finite family with unchanged bounds.

import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Span.Basic

noncomputable section
open Polynomial
open scoped Classical

theorem TranscendenceTheory.bounded_bivariate_relation_basis
    (K A : Type*) [Field K] [CommRing A] [Algebra K A]
    (x y : A) (b s : ℕ) :
    ∃ k : ℕ, k ≤ (b + 1) * (s + 1) ∧
      ∃ H : Fin k → Polynomial (Polynomial K),
        LinearIndependent K H ∧ ∀ P : Polynomial (Polynomial K),
          P ∈ Submodule.span K (Set.range H) ↔
            P.natDegree ≤ s ∧ (∀ i, (P.coeff i).natDegree ≤ b) ∧
              P.eval₂ (Polynomial.aeval x).toRingHom y = 0 := by sorry
