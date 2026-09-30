-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_nilpotent_scalar_multiplication_charpoly
-- name    : WeierstrassEllipticZeta.nilpotent_scalar_multiplication_charpoly
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-12T00:12:35.910474+00:00
-- url     : https://prove2.me/theorems/56220ac0-b4d3-4d2e-a8f1-768468e1c08e
-- title:
--   Characteristic polynomial of multiplication by a scalar plus a nilpotent
-- statement:
--   Let (K) be a field and (A) a finite-dimensional unital (K)-algebra. The algebra (A) need not be commutative or nontrivial. For (a\in A), let (L_a:A\to A) be the (K)-linear map (b\mapsto ab).
--
--   If (z\in K) and (a-z\cdot1_A) is nilpotent, then
--   \[
--   \operatorname{charpoly}(L_a)=(X-z)^{\dim_K A}.
--   \]
--
--   The formula includes dimension zero, when both sides are the constant polynomial (1).
-- source:
--   Derived supporting algebra lemma for the Senthil Kumar mission. If a-z is nilpotent in a finite-dimensional K-algebra A, left multiplication by a has characteristic polynomial (X-z)^dim_K(A). The algebra need not be commutative or nontrivial. Map nilpotence through the regular representation, use the nilpotent characteristic-polynomial theorem, and undo the scalar shift by polynomial composition. This is inferred supporting algebra, not a separately quoted theorem of the source article. Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474: IsNilpotent.charpoly_eq_X_pow_finrank in LinearAlgebra/Eigenspace/Zero.lean; LinearMap.charpoly_sub_smul in LinearAlgebra/Charpoly/Basic.lean. Primary documentation: https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Eigenspace/Zero.html and https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Charpoly/Basic.html . No new definitions or platform dependencies.

import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.LinearAlgebra.Eigenspace.Zero

open Polynomial

theorem WeierstrassEllipticZeta.nilpotent_scalar_multiplication_charpoly
    (K A : Type*) [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    (a : A) (z : K) (h : IsNilpotent (a - algebraMap K A z)) :
    (Algebra.lmul K A a).charpoly = (X - C z) ^ Module.finrank K A := by sorry
