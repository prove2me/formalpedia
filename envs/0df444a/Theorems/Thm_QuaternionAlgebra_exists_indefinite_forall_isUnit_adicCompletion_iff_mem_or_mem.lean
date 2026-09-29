-- Prove2me | Theorems.Thm_QuaternionAlgebra_exists_indefinite_forall_isUnit_adicCompletion_iff_mem_or_mem
-- name    : QuaternionAlgebra.exists_indefinite_forall_isUnit_adicCompletion_iff_mem_or_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/546c82bb-7542-5466-b9c7-b67d4d02ff4e
-- title:
--   Indefinite rational quaternion algebra ramified exactly at q,q'
-- statement:
--   Let $q$ and $q'$ be natural numbers, both prime, with $q'\neq q$. The assertion is the existence of rationals $a,b$ with $0<a$ or $0<b$ such that, for every height-one prime $v$ of the ring of integers $\mathcal O_{\mathbb Q}$, the following two conditions are equivalent: (i) every nonzero element of the $\mathbb Q$-algebra tensor product $\mathbb H[\mathbb Q,a,b]\otimes_{\mathbb Q}\mathbb Q_v$, where $\mathbb Q_v$ denotes the completion of $\mathbb Q$ at $v$ (the `adicCompletion`) and $\mathbb H[\mathbb Q,a,b]$ the quaternion algebra with $i^2=a$, $j^2=b$, is a unit, i.e. the completed algebra is a division algebra; (ii) $q\in v$ or $q'\in v$, that is, $v$ is the prime of $\mathcal O_{\mathbb Q}$ associated with $q$ or with $q'$. Thus the set of finite places at which $\mathbb H[\mathbb Q,a,b]$ is ramified is exactly $\{q,q'\}$, while the sign condition $0<a\vee 0<b$ records that the algebra is split at the real place. The conclusion is stated in terms of the coordinates $a,b$; no normalisation of $a$ and $b$ beyond the stated positivity is asserted.
--
--   This is the existence of the indefinite rational quaternion algebra of reduced discriminant $qq'$, i.e. of a quaternion algebra over $\mathbb Q$ ramified exactly at the even set of places $\{q,q'\}$, presented in explicit Hilbert-symbol coordinates $(a,b)$. It feeds the construction of maximal and Eichler orders in such an algebra used for the Shimura-curve side of the argument, being cited by [`QuaternionAlgebra.exists_isIndefiniteRamifiedExactlyAt_isMaximalOrder_isEichlerOrder_splitting`](thm.html#QuaternionAlgebra.exists_isIndefiniteRamifiedExactlyAt_isMaximalOrder_isEichlerOrder_splitting).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_exists_indefinite_forall_isUnit_adicCompletion_iff_mem_or_mem.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem QuaternionAlgebra.exists_indefinite_forall_isUnit_adicCompletion_iff_mem_or_mem
    (q q' : ℕ) (hq : q.Prime) (hq' : q'.Prime) (hqq' : q' ≠ q) :
    ∃ a b : ℚ, (0 < a ∨ 0 < b) ∧
      ∀ v : HeightOneSpectrum (𝓞 ℚ),
        (∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x) ↔
          ((q : 𝓞 ℚ) ∈ v.asIdeal ∨ (q' : 𝓞 ℚ) ∈ v.asIdeal) := by sorry
