-- Prove2me | Theorems.Thm_PadicInt_natCard_quotient_range_eq_pow_valuation_det
-- name    : PadicInt.natCard_quotient_range_eq_pow_valuation_det
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/7ee1f2c8-d062-5f9a-9e9d-12cdb0a7f2ab
-- title:
--   Index of f(T) equals p^{v(det f)} for ℤₚ-modules
-- statement:
--   Let $p$ be a natural number which is prime, and let $T$ be an additive commutative group equipped with a $\mathbb{Z}_p$-module structure which is free and finitely generated over the $p$-adic integers $\mathbb{Z}_p$. Let $f$ be a $\mathbb{Z}_p$-linear endomorphism of $T$ whose determinant $\det f \in \mathbb{Z}_p$ is nonzero. Then the cardinality of the quotient module $T / \operatorname{range} f$, taken as a natural number via `Nat.card`, equals $p$ raised to the power $v(\det f)$, where $v$ denotes the $p$-adic valuation on $\mathbb{Z}_p$ as a natural-number-valued invariant of a nonzero element. In particular the assertion includes the finiteness of the cokernel, since `Nat.card` of an infinite type would be $0$ while $p^{v(\det f)}$ is positive.
--
--   This is the standard computation of the index of the image of an injective endomorphism of a finite free module over the discrete valuation ring $\mathbb{Z}_p$, in the classical form $[T : f(T)] = |\det f|^{-1}_p$. It is used to count points in the quotient of a Tate module by the kernel of an isogeny-type endomorphism and in the analysis of prime Hecke sets attached to orders in quaternion algebras.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PadicInt_natCard_quotient_range_eq_pow_valuation_det.lean

import Mathlib.LinearAlgebra.Determinant
import Mathlib.NumberTheory.Padics.PadicIntegers

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PadicInt.natCard_quotient_range_eq_pow_valuation_det (p : ℕ) [Fact p.Prime]
    {T : Type*} [AddCommGroup T] [Module ℤ_[p] T] [Module.Free ℤ_[p] T] [Module.Finite ℤ_[p] T]
    (f : Module.End ℤ_[p] T) (hf : LinearMap.det f ≠ 0) :
    Nat.card (T ⧸ LinearMap.range f) = p ^ (LinearMap.det f).valuation := by sorry
