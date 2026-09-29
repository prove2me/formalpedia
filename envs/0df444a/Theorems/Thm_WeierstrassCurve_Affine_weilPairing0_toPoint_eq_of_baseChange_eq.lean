-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_weilPairing0_toPoint_eq_of_baseChange_eq
-- name    : WeierstrassCurve.Affine.weilPairing0_toPoint_eq_of_baseChange_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/06a805f9-830e-5ff3-a0c0-e90cab3e3a45
-- title:
--   Presentation independence of the point-level Weil pairing
-- statement:
--   Let $F_1$, $F_2$ and $\Omega$ be fields, with $\Omega$ algebraically closed and equipped with an $F_1$-algebra and an $F_2$-algebra structure (no compatibility between the two being assumed). Let $W_1$ be a Weierstrass curve over $F_1$ and $W_2$ one over $F_2$, both elliptic, and suppose the base changes coincide, $W_1{/}\Omega = W_2{/}\Omega$, as Weierstrass curves over $\Omega$. Then for every $n \in \mathbb{Z}$ and all $x_1, y_1, x_2, y_2 \in \Omega$, the two values of `weilPairing0`, computed at the points `toPoint` $(W_i{/}\Omega)$ $x_j$ $y_j$ — that is, the affine point $(x_j,y_j)$ when it is nonsingular on $W_i{/}\Omega$ and the point at infinity otherwise — have the same image in $\Omega$. Here `weilPairing0` $W$ $\Omega$ $n$ $S$ $T$ is the unit $c \in \Omega^\times$, chosen if one exists and set to $1$ otherwise, such that translation by $S$ (the $\Omega$-algebra automorphism `transEquiv` of the function field of $W{/}\Omega$) carries `weilFun` $W$ $\Omega$ $n$ $T$ to $c$ times itself; `weilFun` is the quotient of the images of `weilNum` $W$ $\Omega$ $n$ $T$ and `weilNum` $W$ $\Omega$ $n$ $0$ in the function field. The conclusion is stated for the images in $\Omega$ rather than as an equality of units.
--
--   The pairing `weilPairing0` is set up from a presentation of an elliptic curve over a base field $F$ together with an algebraically closed $F$-algebra, yet its values depend only on the curve obtained over that algebraically closed field; this statement records that independence, so that the pairing may be compared across different presentations of one and the same curve over $\Omega$. It is used in the full-level modular curve material, where Weil pairings attached to curves presented over various bases must be identified.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_weilPairing0_toPoint_eq_of_baseChange_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_EllipticCurve_WeilPairingFun

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve ModularCurve.LevelRelabelling WeierstrassCurve WeierstrassCurve.Affine

theorem WeierstrassCurve.Affine.weilPairing0_toPoint_eq_of_baseChange_eq
    {F₁ F₂ Ω : Type*} [Field F₁] [Field F₂] [Field Ω] [Algebra F₁ Ω] [Algebra F₂ Ω]
    [IsAlgClosed Ω] [DecidableEq Ω]
    (W₁ : WeierstrassCurve F₁) (W₂ : WeierstrassCurve F₂) [W₁.IsElliptic] [W₂.IsElliptic]
    (h : W₁⁄Ω = W₂⁄Ω) (n : ℤ) (x₁ y₁ x₂ y₂ : Ω) :
    ((weilPairing0 W₁ Ω n (toPoint (W₁⁄Ω) x₁ y₁) (toPoint (W₁⁄Ω) x₂ y₂) : Ωˣ) : Ω) =
      ((weilPairing0 W₂ Ω n (toPoint (W₂⁄Ω) x₁ y₁) (toPoint (W₂⁄Ω) x₂ y₂) : Ωˣ) : Ω) := by sorry
