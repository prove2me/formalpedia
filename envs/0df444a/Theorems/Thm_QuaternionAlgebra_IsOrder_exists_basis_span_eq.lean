-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsOrder_exists_basis_span_eq
-- name    : QuaternionAlgebra.IsOrder.exists_basis_span_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/4ba25c4a-a9de-5331-8482-0b93a26d4801
-- title:
--   A ℤ-basis of a quaternion order is a ℚ-basis
-- statement:
--   Let $a,b\in\mathbb Q$ and let $\mathbb H[\mathbb Q,a,b]$ be the associated quaternion algebra over $\mathbb Q$. Let $\Lambda$ be a $\mathbb Z$-submodule of $\mathbb H[\mathbb Q,a,b]$ satisfying [`QuaternionAlgebra.IsOrder`](def/QuaternionAlgebra_Order.html#L11), that is: $1\in\Lambda$; $\Lambda$ is closed under multiplication, $x,y\in\Lambda\Rightarrow xy\in\Lambda$; the $\mathbb Q$-span of the underlying set of $\Lambda$ is all of $\mathbb H[\mathbb Q,a,b]$; and $\Lambda$ is finitely generated as a $\mathbb Z$-module. Then there exists a basis $B$ of $\mathbb H[\mathbb Q,a,b]$ as a $\mathbb Q$-vector space, indexed by `Fin 4`, such that every basis vector $B\,i$ lies in $\Lambda$ and the $\mathbb Z$-span of the range of $B$ equals $\Lambda$. Thus a single quadruple $e_1,\dots,e_4$ of elements of $\Lambda$ is simultaneously a $\mathbb Q$-basis of the quaternion algebra and a $\mathbb Z$-basis of the order: $\Lambda=\mathbb Z e_1\oplus\cdots\oplus\mathbb Z e_4$.
--
--   This is the standard structural fact that an order in a rational quaternion algebra is a full lattice of rank $4$, with a $\mathbb Z$-basis that is at the same time a rational basis of the algebra. It supplies the integral coordinate systems used in the description of the adelic completion $\widehat\Lambda$ and its unit group, and is cited by the results on Eichler orders and Hecke sets in the Čerednik–Drinfeld tower.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsOrder_exists_basis_span_eq.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_Order

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped Quaternion

theorem QuaternionAlgebra.IsOrder.exists_basis_span_eq {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    (hΛ : QuaternionAlgebra.IsOrder Λ) :
    ∃ B : Module.Basis (Fin 4) ℚ ℍ[ℚ, a, b], (∀ i, B i ∈ Λ) ∧ Submodule.span ℤ (Set.range B) = Λ := by sorry
