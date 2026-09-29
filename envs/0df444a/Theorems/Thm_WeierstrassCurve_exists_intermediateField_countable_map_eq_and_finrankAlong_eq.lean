-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_intermediateField_countable_map_eq_and_finrankAlong_eq
-- name    : WeierstrassCurve.exists_intermediateField_countable_map_eq_and_finrankAlong_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/78a53ccc-520e-56d2-9896-7cdc04f3b6d3
-- title:
--   Descent of an elliptic curve with a function-field endomorphism to a countable subfield
-- statement:
--   Let $K$ be an algebraically closed field of characteristic $0$ (in a fixed universe), let $E$ be a Weierstrass curve over $K$ which is elliptic, and let $\iota$ be a $K$-algebra homomorphism from the function field of the affine model of $E$ to itself. Assume that $\iota$ is integral as a ring homomorphism, and that `FiniteAlong K ι` holds, i.e. the function field of $E$, regarded as an algebra over itself via $\iota$, is a finite module. Then there exist an intermediate field $K_0$ of $\mathbb{Q} \subseteq K$ with $K_0$ countable, a Weierstrass curve $E_0$ over $K_0$ which is elliptic and whose base change along $K_0 \to K$ equals $E$ (equality of Weierstrass coefficient tuples, not merely isomorphism), and an $\mathrm{AlgebraicClosure}(K_0)$-algebra endomorphism $\iota_0$ of the function field of the affine model of $E_0$ base changed to $\mathrm{AlgebraicClosure}(K_0)$, such that $\iota_0$ is integral as a ring homomorphism, the function field of this base-changed curve is finite as a module over itself via $\iota_0$, and the corresponding rank, $\mathrm{finrankAlong}$ of $\iota_0$, equals the rank $\mathrm{finrankAlong}$ of $\iota$ over $K$.
--
--   This is the Lefschetz-principle descent step for a pair consisting of an elliptic curve and an endomorphism of its function field: the curve and the endomorphism involve only finitely many elements of $K$, hence live over the algebraic closure of a countable (indeed finitely generated over $\mathbb{Q}$) subfield, with the degree of the endomorphism unchanged. It is used in the analysis of isogeny endomorphism data, where the invariance of the degree is transported to a statement about the $j$-invariant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_intermediateField_countable_map_eq_and_finrankAlong_eq.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

universe u

theorem WeierstrassCurve.exists_intermediateField_countable_map_eq_and_finrankAlong_eq
    {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
    (E : WeierstrassCurve K) [E.IsElliptic]
    (ι : E.toAffine.FunctionField →ₐ[K] E.toAffine.FunctionField)
    (hι : ι.toRingHom.IsIntegral) (hfin : FiniteAlong K ι) :
    ∃ (K₀ : IntermediateField ℚ K), Countable K₀ ∧
      ∃ (E₀ : WeierstrassCurve K₀), E₀.IsElliptic ∧ E₀.map (algebraMap K₀ K) = E ∧
        ∃ (ι₀ : (E₀.baseChange (AlgebraicClosure K₀)).toAffine.FunctionField →ₐ[AlgebraicClosure K₀]
            (E₀.baseChange (AlgebraicClosure K₀)).toAffine.FunctionField),
          ι₀.toRingHom.IsIntegral ∧
          ∃ (hfin₀ : FiniteAlong (AlgebraicClosure K₀) ι₀),
            finrankAlong (AlgebraicClosure K₀) ι₀ = finrankAlong K ι := by sorry
