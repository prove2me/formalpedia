-- Prove2me | Theorems.Thm_QuaternionAlgebra_not_forall_isUnit_tensorProduct_adicCompletion_of_forall_prime_ne
-- name    : QuaternionAlgebra.not_forall_isUnit_tensorProduct_adicCompletion_of_forall_prime_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/7ff54ada-2db9-5721-821c-d0096f4d6e35
-- title:
--   Away from p, the ℚᵥ-base change is not division
-- statement:
--   Let $p$ be a prime and let $O$ be a ring which, as a $\mathbb{Z}$-module, is free of finite rank. Assume that for every prime $\ell \neq p$ there exists an isomorphism of $\mathbb{Z}_\ell$-algebras $\mathbb{Z}_\ell \otimes_{\mathbb{Z}} O \cong M_2(\mathbb{Z}_\ell)$ (the hypothesis is stated as nonemptiness of the type of such isomorphisms, for $\ell$ ranging over naturals carrying a primality assumption). Assume further that for rationals $a, b$ there is an isomorphism of $\mathbb{Q}$-algebras $e : \mathbb{Q} \otimes_{\mathbb{Z}} O \cong \mathbb{H}[\mathbb{Q}, a, b]$, the quaternion algebra over $\mathbb{Q}$ with parameters $a$ and $b$. Finally, let $v$ be a point of the height-one spectrum of $\mathcal{O}_{\mathbb{Q}}$, the ring of integers of $\mathbb{Q}$, such that the image of $p$ in $\mathcal{O}_{\mathbb{Q}}$ does not lie in the prime ideal $v$. The conclusion is the negation of the assertion that every nonzero element of $\mathbb{H}[\mathbb{Q}, a, b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$, where $\mathbb{Q}_v$ denotes the adic completion of $\mathbb{Q}$ at $v$, is a unit; that is, this base change fails to be a division ring.
--
--   This is the local statement that a quaternion order which is split at all primes other than $p$ gives a quaternion algebra split at every finite place away from $p$, phrased in the form 'the completed algebra has a nonzero non-unit'. It feeds the construction of a definite quaternion algebra ramified exactly at a prescribed set together with a maximal order, in [`QuaternionAlgebra.exists_isDefiniteRamifiedExactlyAt_isMaximalOrder_range_eq_of_forall_prime_ne`](thm.html#QuaternionAlgebra.exists_isDefiniteRamifiedExactlyAt_isMaximalOrder_range_eq_of_forall_prime_ne).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_not_forall_isUnit_tensorProduct_adicCompletion_of_forall_prime_ne.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion TensorProduct
open IsDedekindDomain NumberField

theorem QuaternionAlgebra.not_forall_isUnit_tensorProduct_adicCompletion_of_forall_prime_ne
    (p : ℕ) [Fact p.Prime] (O : Type*) [Ring O] [Module.Free ℤ O] [Module.Finite ℤ O]
    (hsplit : ∀ ℓ : ℕ, [Fact ℓ.Prime] → ℓ ≠ p →
      Nonempty (ℤ_[ℓ] ⊗[ℤ] O ≃ₐ[ℤ_[ℓ]] Matrix (Fin 2) (Fin 2) ℤ_[ℓ]))
    {a b : ℚ} (e : ℚ ⊗[ℤ] O ≃ₐ[ℚ] ℍ[ℚ, a, b])
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((p : ℕ) : 𝓞 ℚ) ∉ v.asIdeal) :
    ¬ ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x := by sorry
