-- Prove2me | Theorems.Thm_QuaternionAlgebra_exists_isIndefiniteRamifiedExactlyAt_isMaximalOrder_isEichlerOrder_splitting
-- name    : QuaternionAlgebra.exists_isIndefiniteRamifiedExactlyAt_isMaximalOrder_isEichlerOrder_splitting
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/b668410d-4cbf-5630-9f33-0e521720c5de
-- title:
--   Indefinite quaternion algebra ramified at q,q' with Eichler order
-- statement:
--   Let $q$ and $q'$ be primes with $q' \neq q$, and let $N$ be a nonzero natural number divisible by neither $q$ nor $q'$. Then there exist $a,b \in \mathbb{Q}$ with the following properties for the quaternion algebra $\mathbb{H} = \mathbb{H}[\mathbb{Q},a,b]$. First, `IsIndefiniteRamifiedExactlyAt` holds for $a,b,q,q'$: one has $0 < a$ or $0 < b$, and for every height-one prime $v$ of the ring of integers of $\mathbb{Q}$, every nonzero element of $\mathbb{H} \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a unit precisely when $q \in v$ or $q' \in v$. Second, there are $\mathbb{Z}$-submodules $\Lambda, R \subseteq \mathbb{H}$ with $R \le \Lambda$ such that $\Lambda$ is a maximal order — it contains $1$, is closed under multiplication, has $\mathbb{Q}$-span all of $\mathbb{H}$, is finitely generated over $\mathbb{Z}$, and every order containing it equals it — and such that $R$ is an Eichler order of level $N$, meaning $R = \Lambda_1 \sqcap \Lambda_2$ for two maximal orders $\Lambda_1, \Lambda_2$ with the index of $R$ in $\Lambda_1$, as additive subgroups, equal to $N$. Third, there is an injective $\mathbb{Q}$-algebra homomorphism $\iota \colon \mathbb{H} \to M_2(\mathbb{R})$; no compatibility between $\iota$ and $\Lambda$ or $R$ is asserted.
--
--   This is the existence of the arithmetic datum underlying the Shimura curve $X^{qq'}_0(N)$: an indefinite rational quaternion algebra of discriminant $qq'$, a maximal order, an Eichler order of level $N$ inside it, and a real splitting. It is used in the construction of the Čerednik–Drinfeld torsion data that enter Ribet's level-lowering argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_exists_isIndefiniteRamifiedExactlyAt_isMaximalOrder_isEichlerOrder_splitting.lean

import Definitions.Def_CerednikDrinfeld_ShimuraCurve

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped TensorProduct Quaternion NumberField
open QuaternionAlgebra

theorem QuaternionAlgebra.exists_isIndefiniteRamifiedExactlyAt_isMaximalOrder_isEichlerOrder_splitting
    (q q' N : ℕ) (hq : q.Prime) (hq' : q'.Prime) (hqq' : q' ≠ q) (hN : N ≠ 0) (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) :
    ∃ a b : ℚ, IsIndefiniteRamifiedExactlyAt a b q q' ∧
      ∃ Λ R : Submodule ℤ ℍ[ℚ, a, b], IsMaximalOrder Λ ∧ IsEichlerOrder R N ∧ R ≤ Λ ∧
        ∃ ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ, Function.Injective ι := by sorry
