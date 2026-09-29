-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsDefiniteRamifiedExactlyAt_exists_algHom_matrix_ratClosure_injective
-- name    : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt.exists_algHom_matrix_ratClosure_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/529c944a-cfaf-5272-bb7b-86ba72c3df4a
-- title:
--   Splitting of a definite quaternion algebra at a place above r ≠ q
-- statement:
--   Let $a,b \in \mathbb{Q}$ and let $q$ be a prime such that $\mathbb{H} = \mathbb{H}[\mathbb{Q},a,b]$ satisfies [`QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b q`](def/QuaternionAlgebra_EichlerOrder.html#L87), that is: $a < 0$, $b < 0$, and for every height-one prime $v$ of the ring of integers of $\mathbb{Q}$, the algebra $\mathbb{H} \otimes_{\mathbb{Q}} \mathbb{Q}_v$ (the $v$-adic completion) has the property that every non-zero element is a unit precisely when $q$ lies in the prime ideal attached to $v$. Let $r$ be a prime with $r \neq q$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` lying over $r$, in the sense that the image of $r$ in $\overline{\mathbb{Q}}$ belongs to the non-units of $A$. Write $C_A$ for the completion of $\overline{\mathbb{Q}}$ with respect to the valuation of $A$, and let $K_0 =$ [`ValuationSubring.ratClosure A`](def/ValuationSubring_CompletionRatClosure.html#L13) be the topological closure in $C_A$ of the smallest subfield of $C_A$. Then there exists a $\mathbb{Q}$-algebra homomorphism $\iota : \mathbb{H}[\mathbb{Q},a,b] \to M_2(K_0)$ which is injective as a function.
--
--   This is the statement that a definite rational quaternion algebra whose finite ramification locus is exactly $\{q\}$ splits at every other prime, read over the field $K_0$ — a copy of $\mathbb{Q}_r$ — obtained as the closure of $\mathbb{Q}$ inside the completion $C_A$ of $\overline{\mathbb{Q}}$ at a place above $r$. In that form it is used in the construction of Shimura curve models and interchange data in the Čerednik–Drinfeld setting, where $C_A$ is the ground field of the $r$-adic upper half plane and $K_0$ that of the associated Bruhat–Tits tree.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsDefiniteRamifiedExactlyAt_exists_algHom_matrix_ratClosure_injective.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_ValuationSubring_CompletionRatClosure
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem QuaternionAlgebra.IsDefiniteRamifiedExactlyAt.exists_algHom_matrix_ratClosure_injective
    {a b : ℚ} {q : ℕ} [Fact q.Prime] (hdef : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b q)
    {r : ℕ} [Fact r.Prime] (hrq : r ≠ q)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r) :
    ∃ ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A), Function.Injective ι := by sorry
