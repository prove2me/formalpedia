-- Prove2me | Theorems.Thm_TensorProduct_mem_span_unitTmul_of_forall_apply_eq_zero
-- name    : TensorProduct.mem_span_unitTmul_of_forall_apply_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/b54cfd57-e2ca-5a47-9eb9-95fd77e33e61
-- title:
--   Joint zeros in a double base change lie in the span of unit tensors
-- statement:
--   Let $R$ be a commutative ring, $S$ a commutative $R$-algebra, and $K$ a field carrying both an $R$-algebra and an $S$-algebra structure, compatibly in the sense of a scalar tower $R \to S \to K$, and assume the structure map $R \to K$ is injective. Let $T$ be an additive commutative group with an $R$-module structure having no zero smul-divisors, i.e. $r \cdot t = 0$ forces $r = 0$ or $t = 0$. Write $V = K \otimes_S (S \otimes_R T)$ for the iterated base change. Let $\iota$ be an arbitrary index type, let $\Phi_i$ ($i \in \iota$) be $K$-linear endomorphisms of $V$, and let $g_i : T \to T$ be arbitrary functions (no linearity assumed) such that $\Phi_i\bigl(k \otimes_S (1 \otimes_R x)\bigr) = k \otimes_S (1 \otimes_R g_i(x))$ for all $i \in \iota$, $k \in K$ and $x \in T$. Then any $v \in V$ annihilated by every $\Phi_i$ lies in the $K$-span of the set of elements of the form $1 \otimes_S (1 \otimes_R y)$ with $y \in T$ satisfying $g_i(y) = 0$ for all $i$.
--
--   This is an elementary descent statement for a two-step base change of a torsion-free module to a field: a vector killed by a family of operators that act through maps of the underlying module is a $K$-combination of unit tensors coming from the joint zero set of those maps. It is used in the passage from a joint eigenplane condition in a Tate module, base changed to a field of coefficients, to the existence of a rational torsion line, in [`CuspForm.IsNewform.exists_torLine_of_eigenPlane_tateModule_jZero`](thm.html#CuspForm.IsNewform.exists_torLine_of_eigenPlane_tateModule_jZero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TensorProduct_mem_span_unitTmul_of_forall_apply_eq_zero.lean

import Mathlib.LinearAlgebra.TensorProduct.Tower

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped TensorProduct

theorem TensorProduct.mem_span_unitTmul_of_forall_apply_eq_zero
    {R S K T : Type}
    [CommRing R]
    [CommRing S] [Algebra R S]
    [Field K] [Algebra R K] [Algebra S K] [IsScalarTower R S K]
    [AddCommGroup T] [Module R T] [NoZeroSMulDivisors R T]
    (hinj : Function.Injective (algebraMap R K))
    {ι : Type} (Φ : ι → (K ⊗[S] (S ⊗[R] T)) →ₗ[K] (K ⊗[S] (S ⊗[R] T))) (g : ι → T → T)
    (hcomm : ∀ (i : ι) (k : K) (x : T),
      Φ i (k ⊗ₜ[S] ((1 : S) ⊗ₜ[R] x)) = k ⊗ₜ[S] ((1 : S) ⊗ₜ[R] g i x))
    (v : K ⊗[S] (S ⊗[R] T)) (hv : ∀ i, Φ i v = 0) :
    v ∈ Submodule.span K
      {z : K ⊗[S] (S ⊗[R] T) | ∃ y : T, (∀ i, g i y = 0) ∧
        z = (1 : K) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] y)} := by sorry
