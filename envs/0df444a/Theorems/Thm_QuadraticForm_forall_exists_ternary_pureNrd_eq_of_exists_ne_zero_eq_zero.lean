-- Prove2me | Theorems.Thm_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero
-- name    : QuadraticForm.forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/19093cc3-6a05-5e85-9985-d0432eeb00cd
-- title:
--   Isotropic ternary form -ax²-by²+abz² is universal
-- statement:
--   Let $F$ be a field of characteristic zero and let $a,b \in F$ with $a \neq 0$ and $b \neq 0$. Suppose the ternary quadratic form $q(x,y,z) = -a x^2 - b y^2 + a b z^2$ is isotropic over $F$, in the sense that there exist $x,y,z \in F$ for which the conjunction $x = 0 \wedge y = 0 \wedge z = 0$ fails and $-a x^2 - b y^2 + a b z^2 = 0$. Then for every $c \in F$ there exist $x,y,z \in F$ with $-a x^2 - b y^2 + a b z^2 = c$; that is, $q$ represents every element of $F$, including $c = 0$ by the trivial solution. The form is written out explicitly in the coefficients $a$ and $b$ rather than through any quadratic-form structure, and the conclusion is the bare existence of a representation, with no claim that the representing triple is nonzero or otherwise normalised.
--
--   This is the classical statement that an isotropic nondegenerate ternary form is universal, applied to the reduced norm on the pure quaternions of the quaternion algebra $\left(\frac{a,b}{F}\right)$: isotropy produces a hyperbolic plane, which already represents everything. It serves as the representability input for the local–global arguments producing quaternions of prescribed reduced norm, and is cited in the construction of maximal orders and of elements with prescribed square in definite and indefinite quaternion algebras ramified at specified places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem QuadraticForm.forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero
    (F : Type) [Field F] [CharZero F] (a b : F) (ha : a ≠ 0) (hb : b ≠ 0)
    (hiso : ∃ x y z : F, ¬ (x = 0 ∧ y = 0 ∧ z = 0) ∧ -a * x ^ 2 - b * y ^ 2 + a * b * z ^ 2 = 0)
    (c : F) :
    ∃ x y z : F, -a * x ^ 2 - b * y ^ 2 + a * b * z ^ 2 = c := by sorry
