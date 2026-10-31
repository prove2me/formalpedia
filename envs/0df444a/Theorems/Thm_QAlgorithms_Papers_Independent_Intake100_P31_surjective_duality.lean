-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P31_surjective_duality
-- name    : QAlgorithms.Papers.Independent.Intake100.P31.surjective_duality
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:44:38.405886+00:00
-- url     : https://prove2.me/theorems/763efd2c-1008-4658-bc4a-092560c3e40a
-- title:
--   §II.C: dual surjective functions and matrix criterion
-- statement:
--   Let $n\ge1$ and $m\le n$. Let $M$ and $N$ be binary matrices of sizes $m\times n$ and $(n-m)\times n$, respectively, inducing surjective linear maps $f$ and $g$. Then
--
--   $$\ker f=(\ker g)^\perp\quad\Longleftrightarrow\quad MN^{\mathsf T}=0.$$
--
--   This gives a basis-level test for the source's dual pair of surjective hashes. It does not equate the two ordinary universality parameters.
-- source:
--   Dual universality of hash functions and its applications to quantum cryptography, arXiv:1101.0064v4, PDF p. 6, §II.C: dual surjective functions and matrix criterion

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P31

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P31

open scoped BigOperators Matrix ComplexConjugate

open QAlgorithms

local instance {n : ℕ} (C : BinaryLinearCode n) : Fintype C := Fintype.ofFinite C

/-- PDF pp.5--6, surjective duality and its matrix criterion.
The first side of the printed Definition 8 must read dual universal. -/
theorem surjective_duality {n m : ℕ} (hn : 0 < n) (hm : m ≤ n)
    (M : Matrix (Fin m) (Fin n) (ZMod 2))
    (N : Matrix (Fin (n - m)) (Fin n) (ZMod 2))
    (hM : Function.Surjective (Matrix.toLin' M))
    (hN : Function.Surjective (Matrix.toLin' N)) :
    (LinearMap.ker (Matrix.toLin' M) = binDual (LinearMap.ker (Matrix.toLin' N)) ↔
      M * N.transpose = 0) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P31

end
