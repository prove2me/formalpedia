-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_exists_algHom_baseChange_of_isAddCyclic_ker_pointMapOfPushforward
-- name    : WeierstrassCurve.Affine.exists_algHom_baseChange_of_isAddCyclic_ker_pointMapOfPushforward
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/e43a54a4-70bb-5551-8efe-0ba1b5eb4b2c
-- title:
--   Base change of a cyclic kernel of order N
-- statement:
--   Let $R_0$ be a field and let $E_0,E_0'$ be Weierstrass curves over $R_0$ which are elliptic. Let $F$ and $F'$ be algebraically closed fields of characteristic $0$, each an $R_0$-algebra, such that the base changes of $E_0$ and of $E_0'$ to $F$ and to $F'$ are all elliptic, and assume that each of the four base-changed affine curves $W$ carries: a `GenusOnePlaceGate`, i.e. a bijection between $W.\mathrm{Point}$ and the places of $W$'s function field over the base field, all of which have degree $1$; the centring condition `GenusOnePlaceGate.IsCentred`, i.e. for every nonsingular affine point $(x,y)$ the classes of the coordinates $X$ and $Y-y$ lie in the nonunits of the valuation subring of the place attached to $(x,y)$; and `AbelTheorem`, i.e. a divisor of degree $0$ is principal exactly when its divisor sum vanishes. Let $\sigma : F \to F'$ be an $R_0$-algebra map. Let $\iota_0$ be an $F$-algebra map from the function field of $E_0'$ over $F$ to the function field of $E_0$ over $F$, with $\iota_0$ integral, finite in the sense that the target is a finite module over the source via $\iota_0$, and satisfying the pushforward norm formula for divisors along $\iota_0$. Let $N$ be a nonzero natural number, and suppose the kernel of the induced homomorphism on points $(E_0\otimes F).\mathrm{Point} \to (E_0'\otimes F).\mathrm{Point}$ — obtained from the pushforward of degree-zero divisor classes along $\iota_0$ transported through the genus-one identifications of points with $\mathrm{Pic}^0$ — is cyclic as an additive group with $\mathrm{Nat.card}$ equal to $N$. Then there exist an $F'$-algebra map $\iota_1$ from the function field of $E_0'$ over $F'$ to the function field of $E_0$ over $F'$, a proof that $\iota_1$ is integral and a proof that it is finite in the same sense, such that for every proof of the pushforward norm formula along $\iota_1$ the corresponding kernel on points is cyclic with $\mathrm{Nat.card}$ equal to $N$.
--
--   This is the Lefschetz-principle style transfer of a cyclic degree-$N$ function-field correspondence between two elliptic curves from one algebraically closed field of characteristic zero to another over the same base field. It is used in the step deducing that the $j$-invariants of the two curves satisfy the modular polynomial of level $N$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_exists_algHom_baseChange_of_isAddCyclic_ker_pointMapOfPushforward.lean

import Mathlib
import Definitions.Def_Isogeny_ConditionalCurrency
import Definitions.Def_WeierstrassCurve_GenusOnePlaceGateCentred

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve

theorem WeierstrassCurve.Affine.exists_algHom_baseChange_of_isAddCyclic_ker_pointMapOfPushforward
    (R₀ : Type) [Field R₀] (E₀ E₀' : WeierstrassCurve R₀) [E₀.IsElliptic] [E₀'.IsElliptic]
    (F F' : Type) [Field F] [Field F'] [Algebra R₀ F] [Algebra R₀ F']
    [DecidableEq F] [DecidableEq F'] [IsAlgClosed F] [IsAlgClosed F'] [CharZero F] [CharZero F']
    [(E₀.baseChange F).IsElliptic] [(E₀'.baseChange F).IsElliptic]
    [(E₀.baseChange F').IsElliptic] [(E₀'.baseChange F').IsElliptic]
    [GenusOnePlaceGate (E₀.baseChange F).toAffine] [GenusOnePlaceGate.IsCentred (E₀.baseChange F).toAffine]
    [AbelTheorem (E₀.baseChange F).toAffine]
    [GenusOnePlaceGate (E₀'.baseChange F).toAffine] [GenusOnePlaceGate.IsCentred (E₀'.baseChange F).toAffine]
    [AbelTheorem (E₀'.baseChange F).toAffine]
    [GenusOnePlaceGate (E₀.baseChange F').toAffine] [GenusOnePlaceGate.IsCentred (E₀.baseChange F').toAffine]
    [AbelTheorem (E₀.baseChange F').toAffine]
    [GenusOnePlaceGate (E₀'.baseChange F').toAffine] [GenusOnePlaceGate.IsCentred (E₀'.baseChange F').toAffine]
    [AbelTheorem (E₀'.baseChange F').toAffine]
    (σ : F →ₐ[R₀] F')
    (ι₀ : (E₀'.baseChange F).toAffine.FunctionField →ₐ[F] (E₀.baseChange F).toAffine.FunctionField)
    (hι₀ : ι₀.toRingHom.IsIntegral) (hfin₀ : FiniteAlong F ι₀) (hN₀ : NormFormulaAlong F ι₀ hfin₀)
    (N : ℕ) [NeZero N]
    (hcyc : IsAddCyclic (pointMapOfPushforward ι₀ hι₀ hfin₀ hN₀).ker)
    (hcard : Nat.card (pointMapOfPushforward ι₀ hι₀ hfin₀ hN₀).ker = N) :
    ∃ (ι₁ : (E₀'.baseChange F').toAffine.FunctionField →ₐ[F'] (E₀.baseChange F').toAffine.FunctionField)
      (hι₁ : ι₁.toRingHom.IsIntegral) (hfin₁ : FiniteAlong F' ι₁),
      ∀ hN₁ : NormFormulaAlong F' ι₁ hfin₁,
        IsAddCyclic (pointMapOfPushforward ι₁ hι₁ hfin₁ hN₁).ker ∧
          Nat.card (pointMapOfPushforward ι₁ hι₁ hfin₁ hN₁).ker = N := by sorry
