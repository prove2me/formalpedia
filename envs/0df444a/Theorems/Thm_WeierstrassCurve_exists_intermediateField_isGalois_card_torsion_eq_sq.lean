-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_intermediateField_isGalois_card_torsion_eq_sq
-- name    : WeierstrassCurve.exists_intermediateField_isGalois_card_torsion_eq_sq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/39347fe4-8bc3-59a5-bf78-d0c627ef42fc
-- title:
--   Existence of the n-division field of an elliptic curve
-- statement:
--   Let $F$ be a field and let $\Omega$ be a field equipped with an $F$-algebra structure which is algebraically closed and algebraic over $F$ (so an algebraic closure of $F$), let $E$ be a Weierstrass curve over $F$ satisfying `IsElliptic`, and let $n$ be a natural number whose image in $F$ is nonzero. Then there exists an intermediate field $L$ of $\Omega/F$ such that: $L$ is finite-dimensional over $F$; $L$ is Galois over $F$; the subtype of points $P$ of the affine Weierstrass curve obtained by base change of $E$ to $L$ with $n \cdot P = 0$ has cardinality exactly $n^2$ (`Nat.card`, the natural-number cardinality); and the action of $\mathrm{Gal}(L/F)$ on this $n$-torsion is faithful, in the sense that every $F$-algebra automorphism $\sigma$ of $L$ with $\mathrm{Point.map}\,\sigma\,P = P$ for all points $P$ of $E$ over $L$ killed by $n$ is the identity automorphism.
--
--   This is the existence of the $n$-division field $F(E[n])$ inside a fixed algebraic closure: a finite Galois extension of $F$ over which the full $n$-torsion, of order $n^2$, is rational and on which the Galois group acts faithfully. It rests on the project's computation that $E[n](\Omega) \cong (\mathbb{Z}/n)^2$ over an algebraically closed field in which $n$ is invertible, and is used in the Čerednik–Drinfeld part of the development, where division fields of elliptic curves index the relevant level structures.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_intermediateField_isGalois_card_torsion_eq_sq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine

universe u v in

theorem WeierstrassCurve.exists_intermediateField_isGalois_card_torsion_eq_sq
    {F : Type u} {Ω : Type v} [Field F] [Field Ω] [Algebra F Ω] [IsAlgClosed Ω]
    [Algebra.IsAlgebraic F Ω] [DecidableEq Ω]
    (E : WeierstrassCurve F) [E.IsElliptic] {n : ℕ} (hn : (n : F) ≠ 0) :
    ∃ L : IntermediateField F Ω, FiniteDimensional F L ∧ IsGalois F L ∧
      Nat.card {P : (E.baseChange L).toAffine.Point // n • P = 0} = n ^ 2 ∧
      ∀ σ : L ≃ₐ[F] L,
        (∀ P : (E.baseChange L).toAffine.Point, n • P = 0 → Point.map (σ : L →ₐ[F] L) P = P) →
        σ = 1 := by sorry
