-- Prove2me | Theorems.Thm_PDivisibleGroup_Hopf_convPow_apply_mul_eq_sum_of_apply_mul_eq
-- name    : PDivisibleGroup.Hopf.convPow_apply_mul_eq_sum_of_apply_mul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/93a5fa14-9b99-51c7-90b0-efb58bfa81ab
-- title:
--   Higher Leibniz rule for convolution powers of a primitive functional
-- statement:
--   Let $R$ be a commutative semiring, let $A$ be a semiring carrying an $R$-bialgebra structure, and let $\Lambda$ be a commutative $R$-algebra. Let $d \colon A \to \Lambda$ be an $R$-linear map satisfying the hypothesis `hd`, that $d(ab) = \varepsilon(a) \cdot d(b) + \varepsilon(b) \cdot d(a)$ for all $a, b \in A$, where $\varepsilon =$ `Coalgebra.counit` $\colon A \to R$ and the products are the $R$-scalar actions on $\Lambda$; that is, $d$ is a derivation at the unit section of $A$. Convolution powers are formed in the convolution monoid structure on $R$-linear maps $A \to \Lambda$ carried by `WithConv`: for $k \in \mathbb{N}$, the linear map $(\mathrm{WithConv.toConv}\, d ^ k).\mathrm{ofConv}$ is the $k$-th convolution power $d^{*k}$, with $d^{*0} = \eta \circ \varepsilon$ and $(\varphi * \psi)(x) = \mu\big((\varphi \otimes \psi)(\Delta x)\big)$. The assertion is that for every $k \in \mathbb{N}$ and all $a, b \in A$,
--   $$d^{*k}(ab) = \sum_{j=0}^{k} \binom{k}{j}\, d^{*j}(a)\, d^{*(k-j)}(b),$$
--   the binomial coefficients being the images in $\Lambda$ of the natural numbers $\binom{k}{j}$, the sum being indexed by `Finset.range (k + 1)`, and $k - j$ being truncated subtraction of natural numbers.
--
--   This is the higher Leibniz rule for the convolution powers of a primitive functional on a bialgebra, i.e. of a $\Lambda$-valued tangent vector at the origin of the associated affine monoid scheme; dually it expresses $\Delta(P^k) = \sum_j \binom{k}{j} P^j \otimes P^{k-j}$ for a primitive element $P$. It is the algebraic input for forming multiplicative functionals out of (truncated) exponentials $\sum_k c_k d^{*k}$, and is used in the Cartier-duality step [`PDivisibleGroup.CartierDuality.exists_addMonoidHom_tangentSpace_cpoints_pair_eq_sum_pow_of_ker_cotangentModuleProj_eq`](thm.html#PDivisibleGroup.CartierDuality.exists_addMonoidHom_tangentSpace_cpoints_pair_eq_sum_pow_of_ker_cotangentModuleProj_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_Hopf_convPow_apply_mul_eq_sum_of_apply_mul_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v w

theorem PDivisibleGroup.Hopf.convPow_apply_mul_eq_sum_of_apply_mul_eq
    {R : Type u} [CommSemiring R] {A : Type v} [Semiring A] [Bialgebra R A]
    {Λ : Type w} [CommSemiring Λ] [Algebra R Λ] (d : A →ₗ[R] Λ)
    (hd : ∀ a b : A, d (a * b) = Coalgebra.counit (R := R) a • d b + Coalgebra.counit (R := R) b • d a)
    (k : ℕ) (a b : A) :
    (WithConv.toConv d ^ k).ofConv (a * b) =
      ∑ j ∈ Finset.range (k + 1), ((k.choose j : ℕ) : Λ) *
        ((WithConv.toConv d ^ j).ofConv a * (WithConv.toConv d ^ (k - j)).ofConv b) := by sorry
