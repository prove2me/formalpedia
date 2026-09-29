-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_forall_normFormulaAlong_of_isAlgClosed_of_charP_pos
-- name    : WeierstrassCurve.Affine.forall_normFormulaAlong_of_isAlgClosed_of_charP_pos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/88314714-4f17-5f3d-92f9-a0071e71078e
-- title:
--   Pushforward norm formula along isogeny endomorphisms in characteristic p
-- statement:
--   Let $F$ be an algebraically closed field of characteristic $p$ with $p \neq 0$, and let $W$ be an elliptic Weierstrass curve in affine form over $F$. Assume three structures on $W$: a genus-one place gate, that is a bijection `pointEquivPlace` between the points $W(F)$ and the places of $F(W)$ over $F$ together with the statement that every such place has degree $1$; that this gate is centred, meaning that for every nonsingular pair $(x,y)$ the images in $F(W)$ of the coordinate-ring classes of $X - x$ and of $Y - y$ lie in the nonunits of the valuation subring of the place attached to the point $(x,y)$; and Abel's theorem for $W$, namely that a divisor of degree $0$ on $F(W)$ is principal if and only if the sum in the group $W(F)$ of the points corresponding to its places, taken with multiplicities, is zero. The conclusion is that for every isogeny endomorphism datum $D$ of $W$ — an $F$-algebra endomorphism $\iota$ of $F(W)$ which is integral as a ring homomorphism and for which $F(W)$ is a finite module over itself along $\iota$ — the predicate `NormFormulaAlong F D.ι D.hfin` holds: viewing the target $F(W)$ as an algebra over the source $F(W)$ via $\iota$, for every nonzero $f$ in the target, every divisor $E$ on the target with $E(w) = \operatorname{ord}_w(f)$ at all places $w$, and every place $v$ of the source, the pushforward of $E$ has value $\operatorname{ord}_v(\mathrm{N}(f))$ at $v$, where $\mathrm{N}$ is the field norm along $\iota$.
--
--   This is the compatibility of divisor pushforward with the field norm for a self-map of the function field of an elliptic curve, in the positive-characteristic case, where the map may be inseparable and is therefore a composite of a power of Frobenius with a separable extension. It is the characteristic-$p$ half of [`WeierstrassCurve.Affine.forall_normFormulaAlong_of_isAlgClosed`](thm.html#WeierstrassCurve.Affine.forall_normFormulaAlong_of_isAlgClosed), which removes the hypothesis on the characteristic.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_forall_normFormulaAlong_of_isAlgClosed_of_charP_pos.lean

import Mathlib
import Definitions.Def_Isogeny_ConditionalCurrency
import Definitions.Def_WeierstrassCurve_GenusOnePlaceGateCentred

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve

theorem WeierstrassCurve.Affine.forall_normFormulaAlong_of_isAlgClosed_of_charP_pos
    {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F] (p : ℕ) [CharP F p] [NeZero p]
    (W : WeierstrassCurve.Affine F) [W.IsElliptic]
    [GenusOnePlaceGate W] [GenusOnePlaceGate.IsCentred W] [AbelTheorem W] :
    ∀ D : IsogenyEndDatum W, NormFormulaAlong F D.ι D.hfin := by sorry
