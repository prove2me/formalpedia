-- Prove2me | Theorems.Thm_PeriodPair_exists_differentiable_toPoint_comp_eq_pointMapOfPushforward_toPoint
-- name    : PeriodPair.exists_differentiable_toPoint_comp_eq_pointMapOfPushforward_toPoint
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/e5395f79-d46c-5b66-a6aa-c05a04dab723
-- title:
--   Lifting a function-field map of complex tori to an entire function
-- statement:
--   Let $L$ and $L'$ be period pairs, and assume $L.g_2^3 - 27\,L.g_3^2 \neq 0$ and $L'.g_2^3 - 27\,L'.g_3^2 \neq 0$, so that the associated Weierstrass curves $y^2 = x^3 - (g_2/4)x - (g_3/4)$ over $\mathbb{C}$ (with $a_1=a_2=a_3=0$) are elliptic. Each of the two affine curves is assumed to carry: a `GenusOnePlaceGate`, i.e. a bijection between its points and the places of its function field over $\mathbb{C}$, all of these places having degree $1$; the centring condition, i.e. at the place attached to a nonsingular point $(x,y)$ the images in the function field of the coordinate-ring classes of $X$ and of $Y - y$ lie in the nonunits of the valuation subring; and `AbelTheorem`, i.e. a divisor of degree $0$ is principal exactly when its `divisorSum` vanishes. Let $\iota$ be a $\mathbb{C}$-algebra homomorphism from the function field of $L'$'s curve to that of $L$'s curve, with $\iota$ integral as a ring homomorphism, making the target a finite module over the source along $\iota$ (`FiniteAlong`), and satisfying the pushforward norm formula along $\iota$: for every nonzero $f$ in the larger field and every divisor $D$ with $D(w) = \operatorname{ord}_w(f)$ at all places $w$, the pushforward of $D$ satisfies $(\iota_* D)(v) = \operatorname{ord}_v(\mathrm{N}(f))$ at all places $v$ of the smaller field. The conclusion asserts the existence of an entire function $F : \mathbb{C} \to \mathbb{C}$ with $F(0)$ in the lattice of $L'$ such that for every $z \in \mathbb{C}$ one has $\pi_{L'}(F(z)) = \varphi(\pi_L(z))$, where $\pi_L$ denotes the uniformisation $z \mapsto 0$ for $z$ in the lattice and $z \mapsto (\wp(z), \wp'(z))$ otherwise, and $\varphi$ is `pointMapOfPushforward`, the additive homomorphism from the points of $L$'s curve to those of $L'$'s curve obtained by transporting the pushforward along $\iota$ on degree-zero divisor classes through the two genus-one identifications of points with $\mathrm{Pic}^0$.
--
--   This is the analytic lifting statement for a rational map between complex tori: the induced homomorphism on points, defined here divisor-theoretically as a pushforward on $\mathrm{Pic}^0$, is covered by a holomorphic map of the universal covers $\mathbb{C} \to \mathbb{C}$ sending $0$ into the target lattice. It is used in the passage from such a map to the lattice-theoretic data of a scaled sublattice of finite index with cyclic quotient.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PeriodPair_exists_differentiable_toPoint_comp_eq_pointMapOfPushforward_toPoint.lean

import Mathlib
import Definitions.Def_PeriodPair_Uniformization
import Definitions.Def_Isogeny_ConditionalCurrency
import Definitions.Def_WeierstrassCurve_GenusOnePlaceGateCentred

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve

theorem PeriodPair.exists_differentiable_toPoint_comp_eq_pointMapOfPushforward_toPoint
    (L L' : PeriodPair) (hL : L.DiscriminantNeZero) (hL' : L'.DiscriminantNeZero)
    [L.weierstrassCurve.IsElliptic] [L'.weierstrassCurve.IsElliptic]
    [GenusOnePlaceGate L.weierstrassCurve.toAffine] [GenusOnePlaceGate.IsCentred L.weierstrassCurve.toAffine]
    [AbelTheorem L.weierstrassCurve.toAffine]
    [GenusOnePlaceGate L'.weierstrassCurve.toAffine] [GenusOnePlaceGate.IsCentred L'.weierstrassCurve.toAffine]
    [AbelTheorem L'.weierstrassCurve.toAffine]
    (ι : L'.weierstrassCurve.toAffine.FunctionField →ₐ[ℂ] L.weierstrassCurve.toAffine.FunctionField)
    (hι : ι.toRingHom.IsIntegral) (hfin : FiniteAlong ℂ ι) (hN : NormFormulaAlong ℂ ι hfin) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ F 0 ∈ L'.lattice ∧
      ∀ z : ℂ, L'.toPoint hL' (F z) = pointMapOfPushforward ι hι hfin hN (L.toPoint hL z) := by sorry
