-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_isAddCyclic_ker_pointMapOfPushforward_of_baseChange_algHom
-- name    : WeierstrassCurve.Affine.isAddCyclic_ker_pointMapOfPushforward_of_baseChange_algHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/f4d949d7-d2e9-583c-970a-d2c81be54545
-- title:
--   Cyclic kernel of order N descends along base change
-- statement:
--   Let $R_0$ be a field, let $E_0,E_0'$ be elliptic Weierstrass curves over $R_0$, and let $F_1\subseteq F_2$ be algebraically closed $R_0$-algebras of characteristic $0$ forming a scalar tower over $R_0$ (all in one universe), such that the four base changes $E_0\otimes F_i$, $E_0'\otimes F_i$ are elliptic and each of their affine models carries: a `GenusOnePlaceGate`, i.e. a bijection between its group of points and the places of its function field over the base field, all of degree $1$; the centredness condition that at the place attached to a point $(x,y)$ the classes of $X-x$ and $Y-y$ are nonunits of the valuation subring; and `AbelTheorem`, i.e. a degree-zero divisor is principal exactly when its divisor sum vanishes. Let $\chi$, resp. $\chi'$, be $F_1$-algebra maps from the function field of $E_0\otimes F_1$, resp. $E_0'\otimes F_1$, to that of $E_0\otimes F_2$, resp. $E_0'\otimes F_2$, carrying the coordinate function $x$ to $x$ and $y$ to $y$. Let $\iota_1$ be an $F_1$-algebra map from the function field of $E_0'\otimes F_1$ to that of $E_0\otimes F_1$ whose underlying ring map is integral, which makes the target a finite module over the source, and which satisfies the pushforward norm formula (for nonzero $f$ and a divisor $D$ with $D(w)=\mathrm{ord}_w f$ for all places $w$ upstairs, the pushforward of $D$ has value $\mathrm{ord}_v(\mathrm{N}f)$ at each place $v$ downstairs); let $\iota_2$ be the analogous datum over $F_2$, compatible with base change in the sense that $\iota_2(\chi'(x))=\chi(\iota_1(x))$ for all $x$. Let $N$ be a nonzero natural number. If the kernel of the map $(E_0\otimes F_2)(F_2)\to(E_0'\otimes F_2)(F_2)$ induced by divisor pushforward along $\iota_2$ is additively cyclic of cardinality $N$, then the kernel of the corresponding map $(E_0\otimes F_1)(F_1)\to(E_0'\otimes F_1)(F_1)$ induced by pushforward along $\iota_1$ is additively cyclic of cardinality $N$ as well.
--
--   The statement transports the cyclicity and the order of the kernel of an isogeny, realised here as the map on points coming from divisor pushforward along an inclusion of function fields, downwards along an extension of algebraically closed fields of characteristic $0$ over a common base. It is used by [`WeierstrassCurve.Affine.exists_intermediateField_countable_map_eq_of_isAddCyclic_ker_pointMapOfPushforward`](thm.html#WeierstrassCurve.Affine.exists_intermediateField_countable_map_eq_of_isAddCyclic_ker_pointMapOfPushforward), which descends such a configuration to a countable intermediate field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_isAddCyclic_ker_pointMapOfPushforward_of_baseChange_algHom.lean

import Mathlib
import Definitions.Def_Isogeny_ConditionalCurrency
import Definitions.Def_WeierstrassCurve_GenusOnePlaceGateCentred
import Definitions.Def_WeierstrassCurve_FunctionFieldQuadratic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve

universe u

theorem WeierstrassCurve.Affine.isAddCyclic_ker_pointMapOfPushforward_of_baseChange_algHom
    (R₀ : Type u) [Field R₀] (E₀ E₀' : WeierstrassCurve R₀) [E₀.IsElliptic] [E₀'.IsElliptic]
    (F₁ : Type u) [Field F₁] [Algebra R₀ F₁] [DecidableEq F₁] [IsAlgClosed F₁] [CharZero F₁]
    (F₂ : Type u) [Field F₂] [Algebra R₀ F₂] [DecidableEq F₂] [IsAlgClosed F₂] [CharZero F₂]
    [Algebra F₁ F₂] [IsScalarTower R₀ F₁ F₂]
    [(E₀.baseChange F₁).IsElliptic] [(E₀'.baseChange F₁).IsElliptic]
    [(E₀.baseChange F₂).IsElliptic] [(E₀'.baseChange F₂).IsElliptic]
    [GenusOnePlaceGate (E₀.baseChange F₁).toAffine] [GenusOnePlaceGate.IsCentred (E₀.baseChange F₁).toAffine]
    [AbelTheorem (E₀.baseChange F₁).toAffine]
    [GenusOnePlaceGate (E₀'.baseChange F₁).toAffine] [GenusOnePlaceGate.IsCentred (E₀'.baseChange F₁).toAffine]
    [AbelTheorem (E₀'.baseChange F₁).toAffine]
    [GenusOnePlaceGate (E₀.baseChange F₂).toAffine] [GenusOnePlaceGate.IsCentred (E₀.baseChange F₂).toAffine]
    [AbelTheorem (E₀.baseChange F₂).toAffine]
    [GenusOnePlaceGate (E₀'.baseChange F₂).toAffine] [GenusOnePlaceGate.IsCentred (E₀'.baseChange F₂).toAffine]
    [AbelTheorem (E₀'.baseChange F₂).toAffine]
    (χ : (E₀.baseChange F₁).toAffine.FunctionField →ₐ[F₁] (E₀.baseChange F₂).toAffine.FunctionField)
    (hχX : χ (polyToFunctionField (E₀.baseChange F₁).toAffine Polynomial.X)
      = polyToFunctionField (E₀.baseChange F₂).toAffine Polynomial.X)
    (hχY : χ (yCoord (E₀.baseChange F₁).toAffine) = yCoord (E₀.baseChange F₂).toAffine)
    (χ' : (E₀'.baseChange F₁).toAffine.FunctionField →ₐ[F₁] (E₀'.baseChange F₂).toAffine.FunctionField)
    (hχ'X : χ' (polyToFunctionField (E₀'.baseChange F₁).toAffine Polynomial.X)
      = polyToFunctionField (E₀'.baseChange F₂).toAffine Polynomial.X)
    (hχ'Y : χ' (yCoord (E₀'.baseChange F₁).toAffine) = yCoord (E₀'.baseChange F₂).toAffine)
    (ι₁ : (E₀'.baseChange F₁).toAffine.FunctionField →ₐ[F₁] (E₀.baseChange F₁).toAffine.FunctionField)
    (hι₁ : ι₁.toRingHom.IsIntegral) (hfin₁ : FiniteAlong F₁ ι₁) (hN₁ : NormFormulaAlong F₁ ι₁ hfin₁)
    (ι₂ : (E₀'.baseChange F₂).toAffine.FunctionField →ₐ[F₂] (E₀.baseChange F₂).toAffine.FunctionField)
    (hι₂ : ι₂.toRingHom.IsIntegral) (hfin₂ : FiniteAlong F₂ ι₂) (hN₂ : NormFormulaAlong F₂ ι₂ hfin₂)
    (hcompat : ∀ x, ι₂ (χ' x) = χ (ι₁ x))
    (N : ℕ) [NeZero N]
    (hcyc : IsAddCyclic (pointMapOfPushforward ι₂ hι₂ hfin₂ hN₂).ker)
    (hcard : Nat.card (pointMapOfPushforward ι₂ hι₂ hfin₂ hN₂).ker = N) :
    IsAddCyclic (pointMapOfPushforward ι₁ hι₁ hfin₁ hN₁).ker ∧
      Nat.card (pointMapOfPushforward ι₁ hι₁ hfin₁ hN₁).ker = N := by sorry
