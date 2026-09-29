-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsIndefiniteRamifiedExactlyAt_exists_prime_isUnit_natCast_forall_isUnit_tensorProduct_padic
-- name    : QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt.exists_prime_isUnit_natCast_forall_isUnit_tensorProduct_padic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/e2cd2e26-f456-587a-aabb-2dafef19e3c3
-- title:
--   Choice of auxiliary prime ℓ ∈ {q,q'} invertible in a local ring
-- statement:
--   Let $a,b\in\mathbb{Q}$ and let $q,q'$ be natural numbers carrying `Fact` instances asserting their primality, assumed distinct. Suppose the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ satisfies [`QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt a b q q'`](def/CerednikDrinfeld_ShimuraCurve.html#L20), that is: $0<a$ or $0<b$, and for every height-one prime $v$ of the ring of integers of $\mathbb{Q}$, every non-zero element of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ (the $v$-adic completion) is a unit if and only if $q$ or $q'$ lies in the prime ideal $v$. Let $R$ be a commutative local ring. Then there exist a natural number $\ell$ together with a `Fact` instance for its primality such that $\ell=q$ or $\ell=q'$, the image of $\ell$ under the canonical map $\mathbb{N}\to R$ is a unit of $R$, and every non-zero element of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_\ell$ is a unit, i.e. this base change is a division algebra.
--
--   This packages the choice of the auxiliary prime used when proving, by an $\ell$-adic argument, that abelian surfaces with multiplication by an order of an indefinite quaternion algebra ramified exactly at $q$ and $q'$ have potentially good reduction at every place: at a place with local ring $R$ one takes $\ell=q$ unless $q$ is not invertible in $R$, in which case $\ell=q'$. It is cited in the Čerednik–Drinfeld part of the development, in [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_pos_pow_rep_tateModule_eq_one_of_mem_inertiaSubgroupIn`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_pos_pow_rep_tateModule_eq_one_of_mem_inertiaSubgroupIn).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsIndefiniteRamifiedExactlyAt_exists_prime_isUnit_natCast_forall_isUnit_tensorProduct_padic.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_ShimuraCurve

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion TensorProduct

theorem QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt.exists_prime_isUnit_natCast_forall_isUnit_tensorProduct_padic
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hne : q ≠ q')
    (hB : QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt a b q q')
    (R : Type*) [CommRing R] [IsLocalRing R] :
    ∃ (ℓ : ℕ) (_ : Fact ℓ.Prime), (ℓ = q ∨ ℓ = q') ∧ IsUnit (ℓ : R) ∧
      ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] ℚ_[ℓ], x ≠ 0 → IsUnit x := by sorry
