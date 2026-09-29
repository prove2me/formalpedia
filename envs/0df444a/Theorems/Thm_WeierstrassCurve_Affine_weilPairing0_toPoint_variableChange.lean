-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_weilPairing0_toPoint_variableChange
-- name    : WeierstrassCurve.Affine.weilPairing0_toPoint_variableChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/67d24cbf-edaa-50a5-be6a-1d0669174bab
-- title:
--   Invariance of the point-level Weil pairing under coordinate change
-- statement:
--   Let $K$ be an algebraically closed field, $W$ a Weierstrass curve over $K$ that is elliptic, and $C=(u,r,s,t)$ an admissible change of variables over $K$ such that the transformed curve $C\bullet W$ is again elliptic. Let $\ell$ be a prime with $3\le\ell$ and with $\ell\ne 0$ in $K$, and let $D$ be a `LevelPData` over $K$, i.e. a quadruple of coordinates $x_P,y_P,x_Q,y_Q\in K$, satisfying `IsLevelPStructure W ℓ D`: the pairs $(x_P,y_P)$ and $(x_Q,y_Q)$ satisfy the affine Weierstrass equation of $W$, the polynomial $W.\mathrm{pre}\Psi_\ell$ vanishes at $x_P$ and at $x_Q$, and both $\mathrm{indepElt}\,W\,\ell\,x_P\,x_Q=\prod_{a=1}^{(\ell-1)/2}\bigl(x_Q\,(W.\Psi^2_a)(x_P)-(W.\Phi_a)(x_P)\bigr)$ and the same expression with $x_P,x_Q$ interchanged are units. Then the value of `weilPairing0` at parameter $(\ell:\mathbb Z)$, taken on the pair of points of $C\bullet W$ obtained from the transported coordinates $u^{-2}(x-r)$, $u^{-3}(y-s(x-r)-t)$ of $P$ and $Q$ (each read through `toPoint`, which returns the corresponding affine point when the coordinates are nonsingular and $0$ otherwise), equals the value of `weilPairing0` at $(\ell:\mathbb Z)$ on the points of $W$ given by $D.x_P,D.y_P$ and $D.x_Q,D.y_Q$. Here `weilPairing0 W K n S T` is the unit $c\in K^{\times}$, if one exists, with $\mathrm{transEquiv}\,W\,K\,S$ applied to the Weil function $\mathrm{weilFun}\,W\,K\,n\,T$ equal to $c$ times that function, and $1$ otherwise.
--
--   This is the invariance of the point-level Weil pairing of a Katz level-$\ell$ datum under an admissible change of Weierstrass coordinates: the pairing depends only on the pair of $\ell$-torsion points up to isomorphism of Weierstrass models. It is what makes the Weil-pairing value of a full-level moduli class (a raw datum taken up to change of variables) well defined, and it is used in the full-level classification statements about primitive roots, Weil values of classified rigid data, and the counting of maximal ideals over a moduli place.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_weilPairing0_toPoint_variableChange.lean

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_EllipticCurve_WeilPairingFun

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open ModularCurve ModularCurve.LevelRelabelling WeierstrassCurve.Affine

theorem WeierstrassCurve.Affine.weilPairing0_toPoint_variableChange
    {K : Type u} [Field K] [IsAlgClosed K] [DecidableEq K]
    (W : WeierstrassCurve K) [W.IsElliptic] (C : WeierstrassCurve.VariableChange K) [(C • W).IsElliptic]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓK : (ℓ : K) ≠ 0)
    (D : ModularCurve.LevelPData K) (hD : ModularCurve.IsLevelPStructure W ℓ D) :
    weilPairing0 (C • W) K (ℓ : ℤ)
        (toPoint ((C • W).baseChange K) (D.variableChange C).xP (D.variableChange C).yP)
        (toPoint ((C • W).baseChange K) (D.variableChange C).xQ (D.variableChange C).yQ) =
      weilPairing0 W K (ℓ : ℤ) (toPoint (W.baseChange K) D.xP D.yP) (toPoint (W.baseChange K) D.xQ D.yQ) := by sorry
