-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_isPrimitiveRoot_weilPairing0_toPoint_of_isLevelPStructure
-- name    : WeierstrassCurve.Affine.isPrimitiveRoot_weilPairing0_toPoint_of_isLevelPStructure
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/e743a876-1152-570c-9168-6fe4008cf5fa
-- title:
--   Weil pairing of a Katz level-ℓ structure is primitive
-- statement:
--   Let $K$ be an algebraically closed field, $W$ a Weierstrass curve over $K$ whose discriminant is a unit (so that $W$ is elliptic), and let $\ell$ be a prime with $3 \le \ell$ and $\ell \ne 0$ in $K$. Let $D$ be a [`ModularCurve.LevelPData K`](def/ModularCurve_KatzLevelP.html#L43), that is, a quadruple $(x_P, y_P, x_Q, y_Q)$ of elements of $K$, and assume [`ModularCurve.IsLevelPStructure W ℓ D`](def/ModularCurve_KatzLevelP.html#L104): both $(x_P,y_P)$ and $(x_Q,y_Q)$ satisfy the affine Weierstrass equation of $W$, the polynomial $W.\mathrm{pre}\Psi\,\ell$ vanishes at $x_P$ and at $x_Q$, and the two independence elements $\mathrm{indepElt}\,W\,\ell\,x_P\,x_Q = \prod_{a=1}^{(\ell-1)/2}\bigl(x_Q\,(W.\Psi\mathrm{Sq}\,a)(x_P) - (W.\Phi\,a)(x_P)\bigr)$ and $\mathrm{indepElt}\,W\,\ell\,x_Q\,x_P$ are units of $K$. Write $P$ and $Q$ for the points of $W$ base changed to $K$ obtained from these coordinates, namely `Point.some` of the coordinates when they are nonsingular and the point at infinity otherwise. The conclusion is that the value $\mathrm{weilPairing0}\,W\,K\,\ell\,P\,Q \in K^\times$ — the unit scalar $c$ with $\mathrm{transEquiv}_P(\mathrm{weilFun}\,\ell\,Q) = c\cdot \mathrm{weilFun}\,\ell\,Q$, taken to be $1$ if no such $c$ exists — is, viewed in $K$, a primitive $\ell$-th root of unity.
--
--   This is the nondegeneracy of the Weil pairing $e_\ell$ evaluated on a basis of $E[\ell]$, in the form adapted to Katz level-$\ell$ structures: the conditions on the division polynomial and on the independence elements force $(P,Q)$ to be a basis of the $\ell$-torsion, whence $e_\ell(P,Q)$ generates $\mu_\ell$. It is used in the comparison of level-$\ell$ structures with $\mathrm{SL}_2(\mathbb{Z}/\ell)$-orbits and in the identification of cyclotomic factors attached to the moduli package of full level structures.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_isPrimitiveRoot_weilPairing0_toPoint_of_isLevelPStructure.lean

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_EllipticCurve_WeilPairingFun

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open ModularCurve ModularCurve.LevelRelabelling
open WeierstrassCurve.Affine

theorem WeierstrassCurve.Affine.isPrimitiveRoot_weilPairing0_toPoint_of_isLevelPStructure
    {K : Type u} [Field K] [IsAlgClosed K] [DecidableEq K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓK : (ℓ : K) ≠ 0)
    (D : ModularCurve.LevelPData K) (hD : ModularCurve.IsLevelPStructure W ℓ D) :
    IsPrimitiveRoot
      ((weilPairing0 W K ℓ (toPoint (W.baseChange K) D.xP D.yP) (toPoint (W.baseChange K) D.xQ D.yQ) : Kˣ) : K) ℓ := by sorry
