-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_map_algEquiv
-- name    : QuaternionAlgebra.IsMaximalOrder.map_algEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/34777aec-ab48-5cd6-9e45-56ccb16677ed
-- title:
--   Algebra isomorphisms carry maximal orders to maximal orders
-- statement:
--   Let $a,b,a',b'$ be rational numbers and let $e\colon \mathbb{H}[\mathbb{Q},a,b] \to \mathbb{H}[\mathbb{Q},a',b']$ be an isomorphism of $\mathbb{Q}$-algebras between the corresponding rational quaternion algebras. Let $\Lambda$ be a $\mathbb{Z}$-submodule of $\mathbb{H}[\mathbb{Q},a,b]$ satisfying [`QuaternionAlgebra.IsMaximalOrder`](def/QuaternionAlgebra_EichlerOrder.html#L63), that is: (i) $\Lambda$ is an order, meaning $1 \in \Lambda$, $\Lambda$ is closed under multiplication, the $\mathbb{Q}$-span of $\Lambda$ is all of $\mathbb{H}[\mathbb{Q},a,b]$, and $\Lambda$ is finitely generated as a $\mathbb{Z}$-module; and (ii) every order $\Lambda'$ of $\mathbb{H}[\mathbb{Q},a,b]$ with $\Lambda \le \Lambda'$ equals $\Lambda$. The conclusion is that the image of $\Lambda$ under $e$, viewed as a $\mathbb{Z}$-linear map by restriction of scalars, is again a $\mathbb{Z}$-submodule satisfying [`QuaternionAlgebra.IsMaximalOrder`](def/QuaternionAlgebra_EichlerOrder.html#L63) in $\mathbb{H}[\mathbb{Q},a',b']$: it is an order, and no order of $\mathbb{H}[\mathbb{Q},a',b']$ strictly contains it.
--
--   This is the transport of the notion of maximal order along an isomorphism of rational quaternion algebras. It is used in the construction of a maximal order whose image is the ring of rational endomorphisms of a definite quaternionic object, in [`WeierstrassCurve.exists_isMaximalOrder_range_eq_rationalEndSubring_of_isDefiniteRamifiedExactlyAt`](thm.html#WeierstrassCurve.exists_isMaximalOrder_range_eq_rationalEndSubring_of_isDefiniteRamifiedExactlyAt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsMaximalOrder_map_algEquiv.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion

theorem QuaternionAlgebra.IsMaximalOrder.map_algEquiv {a b a' b' : ℚ}
    (e : ℍ[ℚ, a, b] ≃ₐ[ℚ] ℍ[ℚ, a', b']) {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    (hΛ : QuaternionAlgebra.IsMaximalOrder Λ) :
    QuaternionAlgebra.IsMaximalOrder (Λ.map (e.toLinearMap.restrictScalars ℤ)) := by sorry
