-- Prove2me | Theorems.Thm_QuaternionAlgebra_exists_algHom_matrix_injective_of_isDefiniteRamifiedExactlyAt_of_forall_isUnit
-- name    : QuaternionAlgebra.exists_algHom_matrix_injective_of_isDefiniteRamifiedExactlyAt_of_forall_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/27f2b65d-0b74-5134-b749-9557c8f87416
-- title:
--   Quaternion algebra nonsplit at q embeds into M₂(H)
-- statement:
--   Let $a,b,c,d$ be rational numbers and let $q$ be a prime. Assume first that $\mathbb{H}[\mathbb{Q},c,d]$ satisfies [`QuaternionAlgebra.IsDefiniteRamifiedExactlyAt`](def/QuaternionAlgebra_EichlerOrder.html#L87) at $q$, that is: $c<0$, $d<0$, and for every height-one prime $v$ of the ring of integers of $\mathbb{Q}$ the statement that every nonzero element of $\mathbb{H}[\mathbb{Q},c,d]\otimes_{\mathbb{Q}} \mathbb{Q}_v$ (the $v$-adic completion) is a unit holds precisely when $q$ lies in the prime ideal attached to $v$. Assume second that for every height-one prime $v$ of the ring of integers of $\mathbb{Q}$ whose ideal contains $q$, every nonzero element of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a unit; i.e. the completion of $\mathbb{H}[\mathbb{Q},a,b]$ at the place above $q$ is a division algebra. The conclusion is that there exists a homomorphism of $\mathbb{Q}$-algebras $f : \mathbb{H}[\mathbb{Q},a,b] \to M_2(\mathbb{H}[\mathbb{Q},c,d])$, from the quaternion algebra with parameters $a,b$ to the algebra of $2\times 2$ matrices over the quaternion algebra with parameters $c,d$, which is injective as a function.
--
--   This is the algebra-level form of the classical embedding statement: a rational quaternion algebra which is nonsplit at $q$ admits an embedding into $M_2(H)$, where $H$ is the definite rational quaternion algebra ramified exactly at $q$ (over $\mathbb{Q}$, $B$ and $M_2(H)$ then become isomorphic after a suitable base change, and the construction proceeds through a common quadratic subfield). It is used by the refinement [`QuaternionAlgebra.exists_algHom_matrix_injective_forall_apply_mem_of_isOrder_of_isMaximalOrder`](thm.html#QuaternionAlgebra.exists_algHom_matrix_injective_forall_apply_mem_of_isOrder_of_isMaximalOrder), where the embedding is arranged to carry a given order into a maximal order, and it rests on the existence of a quadratic datum in $H$ provided by [`QuaternionAlgebra.exists_isQuadraticDatum_of_sq_lt_four_mul_of_not_isSquare_padic`](thm.html#QuaternionAlgebra.exists_isQuadraticDatum_of_sq_lt_four_mul_of_not_isSquare_padic).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_exists_algHom_matrix_injective_of_isDefiniteRamifiedExactlyAt_of_forall_isUnit.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion TensorProduct
open IsDedekindDomain NumberField

theorem QuaternionAlgebra.exists_algHom_matrix_injective_of_isDefiniteRamifiedExactlyAt_of_forall_isUnit
    {a b c d : ℚ} (q : ℕ) [Fact q.Prime]
    (hH : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt c d q)
    (hBq : ∀ v : HeightOneSpectrum (𝓞 ℚ), (q : 𝓞 ℚ) ∈ v.asIdeal →
      ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x) :
    ∃ f : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d], Function.Injective f := by sorry
