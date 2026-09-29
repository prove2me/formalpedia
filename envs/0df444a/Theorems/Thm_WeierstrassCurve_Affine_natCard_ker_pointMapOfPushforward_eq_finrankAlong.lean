-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_natCard_ker_pointMapOfPushforward_eq_finrankAlong
-- name    : WeierstrassCurve.Affine.natCard_ker_pointMapOfPushforward_eq_finrankAlong
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/edfe241b-5171-5926-b6a3-0a793be30c3d
-- title:
--   Kernel of a pushforward point map has order the degree
-- statement:
--   Let $F$ be an algebraically closed field of characteristic zero, and let $E$, $E'$ be elliptic curves in affine Weierstrass form over $F$. Each of $E$ and $E'$ is assumed to carry a `GenusOnePlaceGate` structure — a bijection between its group of points and the set of places of its function field over $F$ (a place being a valuation subring, distinct from the whole field, containing the image of $F$ and a principal ideal ring), together with the assertion that every such place has degree $1$ — and to satisfy `AbelTheorem`: a divisor of degree zero is principal exactly when its image under `divisorSum` vanishes, where `divisorSum` is the additive map sending a place $v$ to the point corresponding to $v$ under the inverse of that bijection. Let $\iota \colon F(E') \to F(E)$ be an $F$-algebra homomorphism whose underlying ring homomorphism is integral, let `hfin : FiniteAlong F ι` witness that $F(E)$ is a finite module over $F(E')$ via $\iota$, and let `hN` witness the pushforward norm formula along $\iota$: for every nonzero $f \in F(E)$, every divisor $D$ on $F(E)$ with $D(w) = \operatorname{ord}_w(f)$ at all places $w$, and every place $v$ of $F(E')$, the pushforward of $D$ takes the value $\operatorname{ord}_v(N_{F(E)/F(E')}(f))$ at $v$. Then the kernel of `pointMapOfPushforward ι hι hfin hN : E.Point →+ E'.Point` — the homomorphism obtained by transporting points of $E$ to $\mathrm{Pic}^0$ of $F(E)$, pushing degree-zero divisor classes forward along $\iota$, and transporting back to points of $E'$ — has cardinality `finrankAlong F ι`, the dimension of $F(E)$ over $F(E')$ via $\iota$; as the cardinality is taken with `Nat.card`, the equality also records that this kernel is finite.
--
--   This is the statement that an isogeny of elliptic curves in characteristic zero has kernel of order equal to its degree (Silverman III.4.10(c)), here in the form $\#\ker(E(F) \to E'(F)) = [F(E) : \iota F(E')]$ for the point map induced by divisor pushforward. It is used downstream in the analysis of isogeny data, for instance in identifying maps with prescribed kernel and in the recognition of $j$-invariants attached to isogeny endomorphism data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_natCard_ker_pointMapOfPushforward_eq_finrankAlong.lean

import Mathlib
import Definitions.Def_Isogeny_ConditionalCurrency

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve

universe u

theorem WeierstrassCurve.Affine.natCard_ker_pointMapOfPushforward_eq_finrankAlong
    {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
    (E E' : WeierstrassCurve.Affine F) [E.IsElliptic] [GenusOnePlaceGate E] [AbelTheorem E]
    [E'.IsElliptic] [GenusOnePlaceGate E'] [AbelTheorem E']
    (ι : E'.FunctionField →ₐ[F] E.FunctionField) (hι : ι.toRingHom.IsIntegral)
    (hfin : FiniteAlong F ι) (hN : NormFormulaAlong F ι hfin) :
    Nat.card (pointMapOfPushforward ι hι hfin hN).ker = finrankAlong F ι := by sorry
