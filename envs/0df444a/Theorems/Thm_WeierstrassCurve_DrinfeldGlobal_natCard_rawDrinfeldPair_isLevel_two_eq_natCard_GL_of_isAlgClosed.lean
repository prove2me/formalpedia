-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_natCard_rawDrinfeldPair_isLevel_two_eq_natCard_GL_of_isAlgClosed
-- name    : WeierstrassCurve.DrinfeldGlobal.natCard_rawDrinfeldPair_isLevel_two_eq_natCard_GL_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/5543cefc-f38c-53a4-90a7-6812b54eceb1
-- title:
--   Counting level-2 Drinfeld bases over an algebraically closed field
-- statement:
--   Let $A$ be a commutative ring and let $\mathcal G$ be a family of group laws over $A$: for every $A$-algebra $T$, every projective Weierstrass curve $W$ over $T$ and every proof that $\Delta(W)$ is a unit, a relative group law on the projective model of $W$. Assume $\mathcal G$ is chord–tangent, i.e. for all such $T$, $W$, $\Delta(W)$ a unit there is an evaluation $ev$ with `IsPointsEval W (𝒢 T W hΔ) ev`, and that its identity is the origin: there is a ring homomorphism $\chi$ from the origin chart ring of $W$ to $T$ exhibiting the identity section as an origin-chart section and killing the coordinates $x/y$ and $z/y$. Let $\mathcal T$ be a level transport datum at $q=2$, i.e. an operation on raw Drinfeld pairs along $A$-algebra maps and under Weierstrass variable changes, functorial in both and preserving the level-$2$ condition, and assume $\mathcal T$ is a section transport: the transported pair's curve is the expected base change, respectively variable-change twist, and its two sections pull back to the original ones along any graded ring map implementing the coefficient homomorphism, respectively the variable change. Let $\Omega$ be an algebraically closed field which is an $A$-algebra with $2 \neq 0$ in $\Omega$, and let $W_0$ be a Weierstrass curve over $\Omega$ with $\Delta(W_0)$ a unit. Then the number of raw Drinfeld pairs $x$ over $\Omega$ (a curve together with two sections $P,Q$ of its projective model over the base) such that $x$ has curve $W_0$ and, for some proof that $\Delta$ of that curve is a unit, $(x.P, x.Q)$ is a Drinfeld basis of level $2$ for $\mathcal G$ (the basis divisor at $2$ equals the $2$-torsion ideal) equals the cardinality of $\mathrm{GL}_2(\mathbb Z/2)$.
--
--   This is the level-$2$ case of the count of Drinfeld $\Gamma(q)$-bases on an elliptic curve over an algebraically closed field in which $q$ is invertible: the set of such bases is a principal homogeneous space under $\mathrm{GL}_2(\mathbb Z/q)$, here recorded purely as an equality of cardinalities. It feeds the verification of the level-$2$ moduli input in [`ModularCurve.FullLevel.Diamond.natCard_isLevel_rigidDataH1Pow_eq_of_isAlgClosed`](thm.html#ModularCurve.FullLevel.Diamond.natCard_isLevel_rigidDataH1Pow_eq_of_isAlgClosed).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_natCard_rawDrinfeldPair_isLevel_two_eq_natCard_GL_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_LevelRelabelling

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open scoped MatrixGroups

theorem WeierstrassCurve.DrinfeldGlobal.natCard_rawDrinfeldPair_isLevel_two_eq_natCard_GL_of_isAlgClosed
    (A : Type) [CommRing A]
    (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A 𝒢 2) (h𝒯 : 𝒯.IsSectionTransport)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω] [Algebra A Ω] (hqΩ : ((2 : ℕ) : Ω) ≠ 0)
    (W₀ : WeierstrassCurve Ω) (hΔ : IsUnit W₀.Δ) :
    Nat.card {x : RawDrinfeldPair Ω // RawDrinfeldPair.IsLevel 𝒢 2 W₀ x} = Nat.card (GL (Fin 2) (ZMod 2)) := by sorry
