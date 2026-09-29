-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsOrder_finrank_eq_four
-- name    : QuaternionAlgebra.IsOrder.finrank_eq_four
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/1d9de66c-e266-5700-b0dc-8fe2df99be24
-- title:
--   An order in a rational quaternion algebra has ℤ-rank 4
-- statement:
--   Let $a,b$ be rational numbers and let $\mathbb{H}[\mathbb{Q},a,b]$ be the associated quaternion algebra over $\mathbb{Q}$, that is, the $\mathbb{Q}$-algebra with basis $1,i,j,k$ subject to $i^2=a$, $j^2=b$, $k=ij=-ji$. Let $\Lambda$ be a $\mathbb{Z}$-submodule of $\mathbb{H}[\mathbb{Q},a,b]$ which is an order in the sense of the predicate [`QuaternionAlgebra.IsOrder`](def/QuaternionAlgebra_Order.html#L11), i.e. it satisfies the four conditions: $1 \in \Lambda$; $\Lambda$ is closed under multiplication, so $xy \in \Lambda$ whenever $x,y \in \Lambda$; the $\mathbb{Q}$-subspace spanned by the underlying set of $\Lambda$ is all of $\mathbb{H}[\mathbb{Q},a,b]$; and $\Lambda$ is finitely generated as a $\mathbb{Z}$-module. Then the rank of $\Lambda$ as a $\mathbb{Z}$-module, in the sense of `Module.finrank ℤ Λ`, equals $4$. The conclusion records the numerical rank only; freeness of $\Lambda$ and the existence of a $\mathbb{Z}$-basis are not part of this assertion.
--
--   This is the standard fact that an order in a quaternion algebra over $\mathbb{Q}$ is a full $\mathbb{Z}$-lattice, hence of rank $\dim_{\mathbb{Q}} B = 4$. It underlies the construction of explicit $\mathbb{Z}$-bases of orders, via [`QuaternionAlgebra.IsOrder.exists_basis_span_eq`](thm.html#QuaternionAlgebra.IsOrder.exists_basis_span_eq), and is used in the Čerednik–Drinfel'd computations with ideal classes and adelic indices.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsOrder_finrank_eq_four.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_Order

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped Quaternion

theorem QuaternionAlgebra.IsOrder.finrank_eq_four {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    (hΛ : QuaternionAlgebra.IsOrder Λ) : Module.finrank ℤ Λ = 4 := by sorry
