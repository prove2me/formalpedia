-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_natCard_ker_pointMapOfPushforward_eq_finrankAlong_of_separableAlong
-- name    : WeierstrassCurve.Affine.natCard_ker_pointMapOfPushforward_eq_finrankAlong_of_separableAlong
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/f9ad2f4e-3cf6-5f92-b7a7-c9d9ec47936b
-- title:
--   Kernel size of a separable isogeny equals its degree
-- statement:
--   Let $F$ be an algebraically closed field, of arbitrary characteristic, and let $E$ and $E'$ be elliptic curves over $F$ in affine Weierstrass form. Each of $E$, $E'$ is assumed to carry a `GenusOnePlaceGate`, that is a bijection between its group of points and the set of places of its function field over $F$, all of these places having degree $1$, and `AbelTheorem`, asserting that a divisor of degree $0$ on the curve is principal precisely when its associated sum of points vanishes; moreover both function fields are assumed to satisfy `HasPrincipalDivisors`, i.e. every nonzero function $f$ admits a divisor $D$ of degree $0$ with $D(v) = \operatorname{ord}_v(f)$ at every place $v$. Let $\iota : F(E') \to F(E)$ be a homomorphism of $F$-algebras whose underlying ring homomorphism is integral, such that $F(E)$ is a finite module over $F(E')$ through $\iota$ (`hfin`) and is separable over it (`hsep`), and assume the pushforward norm formula along $\iota$: for every nonzero $f \in F(E)$, every divisor $D$ on $F(E)$ with $D(w) = \operatorname{ord}_w(f)$ for all $w$, and every place $v$ of $F(E')$, the pushforward of $D$ takes the value $\operatorname{ord}_v(\mathrm{N}_{F(E)/F(E')}(f))$ at $v$ (`hN`). Then the kernel of the homomorphism $E(F) \to E'(F)$ obtained by composing the Abel–Jacobi identification of $E(F)$ with $\mathrm{Pic}^0(F(E))$, the pushforward of divisor classes along $\iota$, and the inverse Abel–Jacobi identification for $E'$, has cardinality (as a `Nat.card`, so in particular it is finite) equal to $[F(E) : \iota F(E')]$, the rank of $F(E)$ as a module over $F(E')$ via $\iota$.
--
--   This is the statement that a separable isogeny of elliptic curves has as many points in its kernel as its degree, in the form where the isogeny is presented by an inclusion of function fields and the induced map on points is constructed through divisor classes; unlike the characteristic-zero version, separability of $F(E)/\iota F(E')$ is here an explicit hypothesis, as are the two principal-divisor assumptions. It is used in the construction of quotient isogenies, namely in [`WeierstrassCurve.Affine.IsogenyHomDatum.exists_pointHom_comp_eq_of_ker_le_of_separableAlong`](thm.html#WeierstrassCurve.Affine.IsogenyHomDatum.exists_pointHom_comp_eq_of_ker_le_of_separableAlong) and in [`WeierstrassCurve.exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq_of_isAlgClosed`](thm.html#WeierstrassCurve.exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq_of_isAlgClosed).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_natCard_ker_pointMapOfPushforward_eq_finrankAlong_of_separableAlong.lean

import Mathlib
import Definitions.Def_Isogeny_ConditionalCurrency

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve

universe u

theorem WeierstrassCurve.Affine.natCard_ker_pointMapOfPushforward_eq_finrankAlong_of_separableAlong
    {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F]
    (E E' : WeierstrassCurve.Affine F) [E.IsElliptic] [GenusOnePlaceGate E] [AbelTheorem E]
    [E'.IsElliptic] [GenusOnePlaceGate E'] [AbelTheorem E']
    [HasPrincipalDivisors F E.FunctionField] [HasPrincipalDivisors F E'.FunctionField]
    (ι : E'.FunctionField →ₐ[F] E.FunctionField) (hι : ι.toRingHom.IsIntegral)
    (hfin : FiniteAlong F ι) (hsep : SeparableAlong F ι) (hN : NormFormulaAlong F ι hfin) :
    Nat.card (pointMapOfPushforward ι hι hfin hN).ker = finrankAlong F ι := by sorry
