-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_exists_genusOnePlaceGate_isCentred_and_abelTheorem
-- name    : WeierstrassCurve.Affine.exists_genusOnePlaceGate_isCentred_and_abelTheorem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/218538e7-63fe-50ab-a135-d4e19bc04659
-- title:
--   Existence of a centred genus-one place gate with Abel's theorem
-- statement:
--   Let $F$ be an algebraically closed field (with decidable equality) and let $W$ be an affine Weierstrass curve over $F$ which is elliptic, whose coordinate ring `W.CoordinateRing` is a Dedekind domain, and whose function field `W.FunctionField` satisfies [`AlgebraicCurve.HasPrincipalDivisors F W.FunctionField`](def/AlgebraicCurve_DivisorClassGroup.html#L217), i.e. every nonzero $f$ in the function field admits a finitely supported integer-valued function $D$ on the places of $W.FunctionField$ over $F$ with $D(v) = v.\mathrm{ord}\,f$ for every place $v$ and with $\deg D = \sum_v D(v)\,v.\mathrm{deg} = 0$; here a place is a valuation subring of the function field, containing the image of $F$, distinct from the whole field and a principal ideal ring. Then there exists a term $g$ of [`WeierstrassCurve.Affine.GenusOnePlaceGate W`](def/WeierstrassCurve_GenusOnePic0.html#L18), that is, a bijection between the group $W(F)$ of points of $W$ and the set of such places, all of whose places satisfy $v.\mathrm{deg} = 1$, such that moreover, with respect to $g$: (i) the gate is centred, meaning that for all $x, y \in F$ with $W.\mathrm{Nonsingular}\ x\ y$, the images in the function field of the classes of $X - x$ and of $Y - y$ in the coordinate ring lie in the non-units of the valuation subring of the place attached to the point $(x,y)$; and (ii) Abel's theorem holds, i.e. every divisor $D$ of degree $0$ is principal — there is a nonzero $f$ with $D(v) = v.\mathrm{ord}\,f$ for all $v$ — if and only if $\sum_v D(v)\,g^{-1}(v) = O$ in $W(F)$.
--
--   This is the identification of the places of the function field of an elliptic curve over an algebraically closed field with its points, together with Abel's theorem in genus one, which yields the isomorphism $\operatorname{Pic}^0 \cong W(F)$; the centring condition pins the bijection down geometrically, sending an affine point to the valuation centred at it. It supplies the gate instance used downstream in the study of Vélu quotients and modular polynomials, for instance in the results on roots of the modular polynomial at $j$-invariants of isogenous curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_exists_genusOnePlaceGate_isCentred_and_abelTheorem.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_GenusOnePic0
import Definitions.Def_WeierstrassCurve_GenusOnePlaceGateCentred

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

universe u

theorem WeierstrassCurve.Affine.exists_genusOnePlaceGate_isCentred_and_abelTheorem
    {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] {W : WeierstrassCurve.Affine F} [W.IsElliptic]
    [IsDedekindDomain W.CoordinateRing] [AlgebraicCurve.HasPrincipalDivisors F W.FunctionField] :
    ∃ g : WeierstrassCurve.Affine.GenusOnePlaceGate W,
      @WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred F _ W g
        ∧ @WeierstrassCurve.Affine.AbelTheorem F _ _ W g := by sorry
