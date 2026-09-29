-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_pointMapOfPushforward_surjective_of_separableAlong
-- name    : WeierstrassCurve.Affine.pointMapOfPushforward_surjective_of_separableAlong
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/d7e13335-aee6-54ae-a774-ea5c7ff9121f
-- title:
--   Surjectivity of the pushforward point map, separable case
-- statement:
--   Let $F$ be a field and let $E$ and $E'$ be affine Weierstrass curves over $F$, each equipped with a `GenusOnePlaceGate` instance — a bijection of its group of points with the set of places of its function field over $F$, all of whose places have degree $1$ — and with an `AbelTheorem` instance, asserting that a divisor of degree $0$ on the curve is principal (i.e. of the form $v \mapsto \operatorname{ord}_v(f)$ for some nonzero $f$ in the function field) exactly when its image under `divisorSum`, the sum of its coefficients against the points corresponding to its places, vanishes. Let $\iota : F(E') \to F(E)$ be an $F$-algebra homomorphism whose underlying ring homomorphism is integral, and assume: `FiniteAlong`, that $F(E)$ is a finite module over $F(E')$ through $\iota$; `SeparableAlong`, that this algebra is separable; and `NormFormulaAlong`, that for every nonzero $f \in F(E)$, every divisor $D$ on $F(E)$ with $D(w) = \operatorname{ord}_w(f)$ for all $w$, and every place $v$ of $F(E')$, the pushforward divisor satisfies $(\text{pushforward } D)(v) = \operatorname{ord}_v(\mathrm{N}_{F(E)/F(E')}(f))$. Then the homomorphism `pointMapOfPushforward ι hι hfin hN` from $E$-points to $E'$-points, obtained by conjugating the induced pushforward on degree-zero divisor classes by the two point–$\mathrm{Pic}^0$ isomorphisms, is surjective.
--
--   This is the function-field formulation of the statement that a non-constant morphism of curves, in particular an isogeny, is surjective on points, here in a characteristic-free form with separability of the function-field extension as an explicit hypothesis rather than deduced from the base field being algebraically closed of characteristic zero. It is used in the construction and surjectivity of the quotient map by a finite subgroup, notably by [`WeierstrassCurve.fullKernelHom_surjective_of_isAlgClosed`](thm.html#WeierstrassCurve.fullKernelHom_surjective_of_isAlgClosed) and [`WeierstrassCurve.exists_fullKernelHom`](thm.html#WeierstrassCurve.exists_fullKernelHom).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_pointMapOfPushforward_surjective_of_separableAlong.lean

import Mathlib
import Definitions.Def_Isogeny_ConditionalCurrency

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve

universe u

theorem WeierstrassCurve.Affine.pointMapOfPushforward_surjective_of_separableAlong
    {F : Type u} [Field F] [DecidableEq F]
    (E E' : WeierstrassCurve.Affine F) [GenusOnePlaceGate E] [AbelTheorem E]
    [GenusOnePlaceGate E'] [AbelTheorem E']
    (ι : E'.FunctionField →ₐ[F] E.FunctionField) (hι : ι.toRingHom.IsIntegral)
    (hfin : FiniteAlong F ι) (hsep : SeparableAlong F ι) (hN : NormFormulaAlong F ι hfin) :
    Function.Surjective (pointMapOfPushforward ι hι hfin hN) := by sorry
