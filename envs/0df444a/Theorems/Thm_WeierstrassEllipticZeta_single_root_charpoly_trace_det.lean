-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_single_root_charpoly_trace_det
-- name    : WeierstrassEllipticZeta.single_root_charpoly_trace_det
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-12T01:05:10.591932+00:00
-- url     : https://prove2.me/theorems/b6f38694-e131-4185-9a8f-1bbad72111a0
-- title:
--   Trace and determinant for a power of a linear characteristic factor
-- statement:
--   Let $K$ be a field, $M$ a finite-dimensional $K$-vector space, and $f\in\operatorname{End}_K(M)$. Suppose $z\in K$ and $d\in\mathbb N$ satisfy
--   $$\operatorname{charpoly}(f)=(X-z)^d.$$
--   Then
--   $$\operatorname{tr}(f)=d\,z,\qquad \det(f)=z^d.$$
--   No positive-dimension or characteristic-zero assumption is required. The characteristic-polynomial identity itself implies $d=\dim_K M$.
-- source:
--   Derived supporting linear-algebra lemma for the Senthil Kumar mission. For an endomorphism f of a finite-dimensional K-vector space, if charpoly(f)=(X-z)^d then trace(f)=d*z and det(f)=z^d. The exponent d equals the dimension by the characteristic-polynomial degree theorem. Trace is minus nextCoeff, and determinant is the signed constant coefficient. This includes arbitrary fields and dimension zero. This is inferred supporting algebra, not a separately quoted theorem of the source article. Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474: Matrix.trace_eq_neg_charpoly_nextCoeff and Matrix.det_eq_sign_charpoly_coeff in LinearAlgebra/Matrix/Charpoly/Coeff.lean; Polynomial.Monic.nextCoeff_pow in Algebra/Polynomial/Monic.lean; LinearMap.trace_eq_matrix_trace in LinearAlgebra/Trace.lean. Primary documentation: https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Charpoly/Coeff.html , https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Polynomial/Monic.html , and https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Trace.html . No new definitions or platform dependencies.

import Mathlib.Algebra.Polynomial.Monic
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Trace

open Polynomial

theorem WeierstrassEllipticZeta.single_root_charpoly_trace_det
    (K M : Type*) [Field K] [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    (f : Module.End K M) (z : K) (d : ℕ)
    (h : f.charpoly = (X - C z) ^ d) :
    LinearMap.trace K M f = (d : K) * z ∧ f.det = z ^ d := by sorry
