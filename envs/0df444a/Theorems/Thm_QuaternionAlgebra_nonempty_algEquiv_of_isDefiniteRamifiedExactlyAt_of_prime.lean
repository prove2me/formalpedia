-- Prove2me | Theorems.Thm_QuaternionAlgebra_nonempty_algEquiv_of_isDefiniteRamifiedExactlyAt_of_prime
-- name    : QuaternionAlgebra.nonempty_algEquiv_of_isDefiniteRamifiedExactlyAt_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/e8fbf691-9599-5526-8652-ededd8271766
-- title:
--   Uniqueness of the definite rational quaternion algebra ramified at q
-- statement:
--   Let $a,b,a',b'$ be rational numbers and let $q$ be a prime natural number. Assume that the pair $(a,b)$ satisfies [`QuaternionAlgebra.IsDefiniteRamifiedExactlyAt`](def/QuaternionAlgebra_EichlerOrder.html#L87) at $q$, that is: $a<0$, $b<0$, and for every height-one prime $v$ of the ring of integers of $\mathbb{Q}$, the base change $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ to the $v$-adic completion has the property that each of its nonzero elements is a unit if and only if the image of $q$ lies in the prime ideal attached to $v$. Assume the same predicate for $(a',b')$ with the same $q$: $a'<0$, $b'<0$, and for each $v$ the algebra $\mathbb{H}[\mathbb{Q},a',b']\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a division algebra in the above sense exactly when $v$ contains $q$. The conclusion is that the type of $\mathbb{Q}$-algebra isomorphisms $\mathbb{H}[\mathbb{Q},a,b]\simeq\mathbb{H}[\mathbb{Q},a',b']$ is nonempty, i.e. the two quaternion algebras $\left(\frac{a,b}{\mathbb{Q}}\right)$ and $\left(\frac{a',b'}{\mathbb{Q}}\right)$ are isomorphic as $\mathbb{Q}$-algebras.
--
--   This is the uniqueness half, specialised to $\mathbb{Q}$ and to definite algebras of prime discriminant, of the classification of quaternion algebras over a number field by their set of ramified places (Hasse–Brauer–Noether); over $\mathbb{Q}$ it is deduced from Hilbert reciprocity together with the local–global principle for ternary quadratic forms. It is used in the construction of a maximal order whose image is the rational endomorphism subring of a suitable Weierstrass curve, via [`WeierstrassCurve.exists_isMaximalOrder_range_eq_rationalEndSubring_of_isDefiniteRamifiedExactlyAt`](thm.html#WeierstrassCurve.exists_isMaximalOrder_range_eq_rationalEndSubring_of_isDefiniteRamifiedExactlyAt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_nonempty_algEquiv_of_isDefiniteRamifiedExactlyAt_of_prime.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem QuaternionAlgebra.nonempty_algEquiv_of_isDefiniteRamifiedExactlyAt_of_prime
    (a b a' b' : ℚ) (q : ℕ) (hq : q.Prime)
    (h : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b q) (h' : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a' b' q) :
    Nonempty (ℍ[ℚ, a, b] ≃ₐ[ℚ] ℍ[ℚ, a', b']) := by sorry
