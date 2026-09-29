-- Prove2me | Theorems.Thm_QuaternionAlgebra_exists_nrd_eq_of_pos_of_isDefiniteRamifiedExactlyAt_two
-- name    : QuaternionAlgebra.exists_nrd_eq_of_pos_of_isDefiniteRamifiedExactlyAt_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/6e6e9927-00b5-57f4-8755-fb7d1a5f2d3c
-- title:
--   Reduced norms of the definite algebra ramified at 2
-- statement:
--   Let $a,b$ be rational numbers and let $\mathbb{H}[\mathbb{Q},a,b]$ denote the quaternion algebra over $\mathbb{Q}$ with generators $i,j$ satisfying $i^2=a$, $j^2=b$, $ji=-ij$. Assume the predicate [`QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b 2`](def/QuaternionAlgebra_EichlerOrder.html#L87), that is: $a<0$, $b<0$, and for every height-one prime $v$ of the ring of integers of $\mathbb{Q}$, the base change $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ to the $v$-adic completion has all its nonzero elements invertible exactly when the image of $2$ in the ring of integers lies in the prime ideal of $v$; in other words, the completion at $v$ is a division algebra precisely for $v$ the place above $2$. Let $t$ be a rational number with $0<t$. Then there exists $\gamma\in\mathbb{H}[\mathbb{Q},a,b]$ whose reduced norm equals $t$, where the reduced norm of $\gamma$ is the value $\gamma_{\mathrm{re}}^2-a\,\gamma_{i}^2-b\,\gamma_{j}^2+ab\,\gamma_{k}^2$ of the norm form on the coordinates of $\gamma$ in the basis $1,i,j,k$.
--
--   This is the case of discriminant $2$ of the Hasse–Schilling–Eichler norm theorem for a definite quaternion algebra over $\mathbb{Q}$: the reduced norms from such an algebra are exactly the positive rationals, and for the Hamilton quaternions the surjectivity onto positive rationals specialises to Lagrange's four-square theorem. It is used in the treatment of Eichler orders, where elements of prescribed reduced norm are needed to move finite idèles into the stabiliser of an order and to decompose idelic double cosets.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_exists_nrd_eq_of_pos_of_isDefiniteRamifiedExactlyAt_two.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion

theorem QuaternionAlgebra.exists_nrd_eq_of_pos_of_isDefiniteRamifiedExactlyAt_two
    {a b : ℚ} (hdef : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b 2)
    (t : ℚ) (ht : 0 < t) :
    ∃ γ : ℍ[ℚ, a, b], QuaternionAlgebra.nrd γ = t := by sorry
