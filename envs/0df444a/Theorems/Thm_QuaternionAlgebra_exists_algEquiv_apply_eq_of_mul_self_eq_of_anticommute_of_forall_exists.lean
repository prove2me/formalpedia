-- Prove2me | Theorems.Thm_QuaternionAlgebra_exists_algEquiv_apply_eq_of_mul_self_eq_of_anticommute_of_forall_exists
-- name    : QuaternionAlgebra.exists_algEquiv_apply_eq_of_mul_self_eq_of_anticommute_of_forall_exists
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/1a155003-dad3-5fe7-8556-b0961a1234dd
-- title:
--   Recognising H[ℚ,t,s] from an anticommuting spanning pair
-- statement:
--   Let $a,b$ and $t,s$ be rational numbers with $t \neq 0$ and $s \neq 0$, and work in the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ over $\mathbb{Q}$, whose standard generators satisfy $i^2 = a$, $j^2 = b$, $ij = -ji$. Suppose given two elements $x, w \in \mathbb{H}[\mathbb{Q},a,b]$ such that $x^2$ is the image of $t$ under the structure map $\mathbb{Q} \to \mathbb{H}[\mathbb{Q},a,b]$, $w^2$ is the image of $s$, and $x$ and $w$ anticommute, $xw = -(wx)$; suppose moreover that $1, x, w, xw$ span $\mathbb{H}[\mathbb{Q},a,b]$ over $\mathbb{Q}$, in the explicit sense that every $u$ can be written as $\alpha \cdot 1 + \beta x + \gamma w + \delta (xw)$ with $\alpha, \beta, \gamma, \delta \in \mathbb{Q}$. The conclusion is that there exists an isomorphism of $\mathbb{Q}$-algebras $e : \mathbb{H}[\mathbb{Q},t,s] \to \mathbb{H}[\mathbb{Q},a,b]$ carrying the generator $i = \langle 0,1,0,0 \rangle$ of $\mathbb{H}[\mathbb{Q},t,s]$ to $x$ and the generator $j = \langle 0,0,1,0 \rangle$ to $w$.
--
--   This is the standard recognition criterion for a quaternion algebra in terms of a quaternionic basis: an anticommuting pair of elements with rational squares $t, s$ spanning the algebra together with $1$ and their product identifies it with the symbol algebra $(t,s/\mathbb{Q})$. It is used in the construction of algebra homomorphisms from an indefinite quaternion algebra, ramified exactly at a prescribed set of places, into a matrix algebra.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_exists_algEquiv_apply_eq_of_mul_self_eq_of_anticommute_of_forall_exists.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion

theorem QuaternionAlgebra.exists_algEquiv_apply_eq_of_mul_self_eq_of_anticommute_of_forall_exists
    {a b : ℚ} (t s : ℚ) (ht : t ≠ 0) (hs : s ≠ 0) (x w : ℍ[ℚ, a, b])
    (hx : x * x = algebraMap ℚ ℍ[ℚ, a, b] t) (hw : w * w = algebraMap ℚ ℍ[ℚ, a, b] s) (hxw : x * w = -(w * x))
    (hspan : ∀ u : ℍ[ℚ, a, b], ∃ α β γ δ : ℚ, u = α • 1 + β • x + γ • w + δ • (x * w)) :
    ∃ e : ℍ[ℚ, t, s] ≃ₐ[ℚ] ℍ[ℚ, a, b], e ⟨0, 1, 0, 0⟩ = x ∧ e ⟨0, 0, 1, 0⟩ = w := by sorry
