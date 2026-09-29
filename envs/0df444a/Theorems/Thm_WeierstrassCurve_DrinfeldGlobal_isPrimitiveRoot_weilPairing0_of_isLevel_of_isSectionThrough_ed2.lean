-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isPrimitiveRoot_weilPairing0_of_isLevel_of_isSectionThrough_ed2
-- name    : WeierstrassCurve.DrinfeldGlobal.isPrimitiveRoot_weilPairing0_of_isLevel_of_isSectionThrough_ed2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/441de46e-d429-566f-ba13-c0bf72573791
-- title:
--   Weil pairing of a Drinfeld Γ(q)-basis is primitive
-- statement:
--   Let $A$ be a commutative ring and $\mathcal G$ a family of relative group laws attaching, to every $A$-algebra $T$ and every projective Weierstrass curve over $T$ with unit discriminant, a relative group law on its projective model; assume $\mathcal G$ is chord–tangent (each such group law admits a points-evaluation `ev`) and has the origin as identity (the identity section is cut out by a ring homomorphism from the origin chart ring killing `xOverY` and `zOverY`). Let $q$ be a prime with $3 \le q$, and let $\mathcal T$ be a level transport for $(\mathcal G,q)$ — an action on raw Drinfeld pairs by $A$-algebra maps and by variable changes, compatible with the level condition — satisfying `IsSectionTransport`, i.e. the transported pairs' sections pull back to the original ones along the corresponding maps of projective models. Let $K_0$ be a field and $A$-algebra with $q \ne 0$ in $K_0$, let $\Omega$ be an algebraically closed field over $K_0$ (with decidable equality), and let $W$ be an elliptic projective Weierstrass curve over $K_0$. Let $x$ be a raw Drinfeld pair over $K_0$ (a projective Weierstrass curve `x.curve` together with two sections `x.P`, `x.Q`) which is of level $q$ for $W$: `x.curve = W` and, for a witness that `x.curve.Δ` is a unit, $(x.P,x.Q)$ is a Drinfeld basis of level $q$ for $\mathcal G\,K_0\,x.curve$. Let $D$ consist of four elements $x_P,y_P,x_Q,y_Q$ of $K_0$ such that `x.P` passes through $(x_P,y_P)$ and `x.Q` through $(x_Q,y_Q)$, in the sense that each section is cut out by a ring homomorphism from the $Z$-chart ring of `x.curve` to $K_0$ whose affine coordinates are the indicated values. Then the value in $\Omega$ of the unit `weilPairing0 W Ω q` evaluated at the affine points of $W$ over $\Omega$ determined by $(x_P,y_P)$ and $(x_Q,y_Q)$ (via `toPoint`, which returns `Point.some` at a nonsingular pair of coordinates and $0$ otherwise, applied to the images under $K_0 \to \Omega$) is a primitive $q$-th root of unity.
--
--   This is the statement that a Drinfeld $\Gamma(q)$-structure on an elliptic curve over a field in which $q$ is invertible is an honest basis of the $q$-torsion, so that its Weil pairing is a primitive $q$-th root of unity — the nondegeneracy input for level-$q$ moduli. It is used in the analysis of full level structures and of the diamond/determinant action on them, where the pairing identifies the determinant of a change of basis.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_isPrimitiveRoot_weilPairing0_of_isLevel_of_isSectionThrough_ed2.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_EllipticCurve_WeilPairingFun

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal
open ModularCurve ModularCurve.LevelRelabelling
open WeierstrassCurve.Affine

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.isPrimitiveRoot_weilPairing0_of_isLevel_of_isSectionThrough_ed2
    (A : Type) [CommRing A] (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (q : ℕ) [Fact q.Prime] (hq3 : 3 ≤ q)
    (𝒯 : LevelTransport A 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)
    {K₀ : Type} [Field K₀] [Algebra A K₀] (hqK : ((q : ℕ) : K₀) ≠ 0)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω] [Algebra K₀ Ω]
    (W : WeierstrassCurve.Projective K₀) [WeierstrassCurve.IsElliptic W]
    (x : RawDrinfeldPair K₀) (hx : RawDrinfeldPair.IsLevel 𝒢 q W x)
    (D : ModularCurve.LevelPData K₀)
    (hP : IsSectionThrough x.P D.xP D.yP) (hQ : IsSectionThrough x.Q D.xQ D.yQ) :
    IsPrimitiveRoot
      ((weilPairing0 W Ω q
          (toPoint (W⁄Ω) (algebraMap K₀ Ω D.xP) (algebraMap K₀ Ω D.yP))
          (toPoint (W⁄Ω) (algebraMap K₀ Ω D.xQ) (algebraMap K₀ Ω D.yQ)) : Ωˣ) : Ω) q := by sorry
