-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_pointMapOfPushforward_surjective
-- name    : WeierstrassCurve.Affine.pointMapOfPushforward_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/da89fd8d-d346-53a0-8175-51c3792e69dc
-- title:
--   Pushforward map on points of an elliptic curve is surjective
-- statement:
--   Let $F$ be an algebraically closed field of characteristic zero and let $E$, $E'$ be affine Weierstrass curves over $F$, both elliptic, and both equipped with the two genus-one gates: a bijection of the point set with the set of places of the function field over $F$ (a place being a proper valuation subring of the function field which contains the image of $F$ and is a principal ideal ring) under which every place has degree $1$, and the Abel-type property that a divisor of degree $0$ is principal, i.e. of the form $v \mapsto v.\mathrm{ord}(f)$ for some $f \neq 0$, exactly when the sum in the group of points of its places, weighted by their multiplicities, vanishes. Let $\iota \colon F(E') \to F(E)$ be an $F$-algebra map whose underlying ring map is integral, assume $F(E)$ is a finite module over $F(E')$ via $\iota$, and assume the pushforward norm formula along $\iota$: for every nonzero $f \in F(E)$ and every divisor $D$ on $F(E)$ with $D(w) = w.\mathrm{ord}(f)$ at all places $w$, and every place $v$ of $F(E')$, the pushforward of $D$ takes at $v$ the value $v.\mathrm{ord}(\mathrm{N}_{F(E)/F(E')}(f))$. Then the group homomorphism $E(F) \to E'(F)$ obtained by transporting the pushforward of degree-zero divisor classes along $\iota$ through the genus-one identifications $\mathrm{Pic}^0 \cong \mathrm{Point}$ is surjective.
--
--   This is the function-field form of the statement that a nonconstant morphism of elliptic curves over an algebraically closed field is surjective on points (Silverman, III.4.10(a)), here for the map on points induced by divisor pushforward along an embedding of function fields. It feeds the computation of the kernel of that map, in particular its cardinality in terms of the degree of $F(E)/F(E')$, and thence the comparison of isogeny kernels used downstream.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_pointMapOfPushforward_surjective.lean

import Mathlib
import Definitions.Def_Isogeny_ConditionalCurrency

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve

universe u

theorem WeierstrassCurve.Affine.pointMapOfPushforward_surjective
    {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
    (E E' : WeierstrassCurve.Affine F) [E.IsElliptic] [GenusOnePlaceGate E] [AbelTheorem E]
    [E'.IsElliptic] [GenusOnePlaceGate E'] [AbelTheorem E']
    (ι : E'.FunctionField →ₐ[F] E.FunctionField) (hι : ι.toRingHom.IsIntegral)
    (hfin : FiniteAlong F ι) (hN : NormFormulaAlong F ι hfin) :
    Function.Surjective (pointMapOfPushforward ι hι hfin hN) := by sorry
