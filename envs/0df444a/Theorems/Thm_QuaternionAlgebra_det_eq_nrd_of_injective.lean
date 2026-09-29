-- Prove2me | Theorems.Thm_QuaternionAlgebra_det_eq_nrd_of_injective
-- name    : QuaternionAlgebra.det_eq_nrd_of_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/dae505da-7574-5224-a3c9-bfae286ba866
-- title:
--   Determinant of a real matrix representation equals the reduced norm
-- statement:
--   Let $a,b$ be non-zero rational numbers and let $\mathbb{H}[\mathbb{Q},a,b]$ be the associated rational quaternion algebra, with basis $1,i,j,k$ satisfying $i^2=a$, $j^2=b$. Let $\iota : \mathbb{H}[\mathbb{Q},a,b] \to M_2(\mathbb{R})$ be a homomorphism of $\mathbb{Q}$-algebras which is injective as a map of sets, and let $x$ be an element of $\mathbb{H}[\mathbb{Q},a,b]$. Then the determinant of the real $2\times 2$ matrix $\iota(x)$ equals the image in $\mathbb{R}$ of the rational number $\mathrm{nrd}(x)$, where `nrd` is defined by the explicit formula $$\mathrm{nrd}(x)=x_{\mathrm{re}}^2-a\,x_{\mathrm{imI}}^2-b\,x_{\mathrm{imJ}}^2+ab\,x_{\mathrm{imK}}^2$$ in the coordinates of $x$ with respect to the basis $1,i,j,k$. No hypothesis of surjectivity, of $\iota$ being an isomorphism onto $M_2(\mathbb{R})$, or of $\mathbb{H}[\mathbb{Q},a,b]$ being a division algebra is imposed: injectivity of $\iota$ together with $a\neq 0$ and $b\neq 0$ suffices.
--
--   This is the standard identification of the reduced norm of a quaternion algebra with the determinant under a splitting, here in the concrete form needed for real matrix realisations of rational quaternion algebras. It is used throughout the Čerednik–Drinfeld part of the development, for instance in the construction of fake elliptic curves and in the comparison of quaternionic units with Fuchsian subgroups of $\mathrm{GL}_2(\mathbb{R})$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_det_eq_nrd_of_injective.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_CerednikDrinfeld_ShimuraCurve

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups Quaternion
open QuaternionAlgebra CerednikDrinfeld

theorem QuaternionAlgebra.det_eq_nrd_of_injective
    {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι) (x : ℍ[ℚ, a, b]) :
    (ι x).det = ((nrd x : ℚ) : ℝ) := by sorry
