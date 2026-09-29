-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_mul_mem_line_of_line_of_prime
-- name    : QuaternionAlgebra.IsMaximalOrder.exists_mul_mem_line_of_line_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/153ab571-d306-56c0-88aa-b6c08633dc87
-- title:
--   Transitivity on Λ-lines mod m, including ramified ℓ
-- statement:
--   Let $q$ and $q'$ be primes with $q' \neq q$, and let $a, b \in \mathbb{Q}$ be such that the quaternion algebra $B = \mathbb{H}[\mathbb{Q}, a, b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`: that is, $0 < a$ or $0 < b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the completed algebra $B \otimes_{\mathbb{Q}} \mathbb{Q}_v$ has all its nonzero elements invertible exactly when $q \in v$ or $q' \in v$. Let $\Lambda \subseteq B$ be a $\mathbb{Z}$-submodule which is a maximal order, i.e. $1 \in \Lambda$, $\Lambda$ is closed under multiplication, finitely generated, spans $B$ over $\mathbb{Q}$, and is maximal among the submodules with these properties. Let $\ell$ be a prime and $m \neq 0$ a natural number divisible by $\ell$. Let $L_0$ and $L$ be $\mathbb{Z}$-submodules of $B$, each contained in $\Lambda$, each containing $\ell \cdot x$ for every $x \in \Lambda$, each stable under left multiplication by elements of $\Lambda$, and each of relative index $\ell^2$ in $\Lambda$ as additive subgroups. Then there exist $c, d \in \Lambda$ with $cd - 1 = m \cdot y$ and $dc - 1 = m \cdot y'$ for some $y, y' \in \Lambda$, such that $xc \in L$ for every $x \in L_0$, and $xd \in L_0$ for every $x \in L$.
--
--   In classical terms: the units of $\Lambda/m\Lambda$ act transitively on the left $\Lambda$-stable lines of $\Lambda/\ell\Lambda$, with no hypothesis separating $\ell$ from the ramified primes $q, q'$ — at a ramified $\ell$ the quotient $\Lambda/\ell\Lambda$ is local with a unique such line, so the statement is vacuous there, while at the remaining primes it is the transitivity of $\mathrm{GL}_2(\mathbb{Z}/m)$ on lines of $(\mathbb{Z}/\ell)^2$. It feeds the construction of full level structures on fake elliptic curves in the Čerednik–Drinfeld part of the development, being cited by [`CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.exists_fullLevel_forall_factorsThrough_iff`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.exists_fullLevel_forall_factorsThrough_iff) and [`CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_flat_surjective_withFullLevel_forall_factorsThrough_iff`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_flat_surjective_withFullLevel_forall_factorsThrough_iff).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsMaximalOrder_exists_mul_mem_line_of_line_of_prime.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem QuaternionAlgebra.IsMaximalOrder.exists_mul_mem_line_of_line_of_prime
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (m : ℕ) (hm : m ≠ 0) (hℓm : ℓ ∣ m)
    (L₀ : Submodule ℤ ℍ[ℚ, a, b]) (hL₀ : L₀ ≤ Λ) (hℓL₀ : ∀ x : ↥Λ, (ℓ : ℚ) • (x : ℍ[ℚ, a, b]) ∈ L₀)
    (hL₀_left : ∀ (y : ↥Λ) (x : ℍ[ℚ, a, b]), x ∈ L₀ → (y : ℍ[ℚ, a, b]) * x ∈ L₀)
    (hL₀_index : L₀.toAddSubgroup.relIndex Λ.toAddSubgroup = ℓ ^ 2)
    (L : Submodule ℤ ℍ[ℚ, a, b]) (hL : L ≤ Λ) (hℓL : ∀ x : ↥Λ, (ℓ : ℚ) • (x : ℍ[ℚ, a, b]) ∈ L)
    (hL_left : ∀ (y : ↥Λ) (x : ℍ[ℚ, a, b]), x ∈ L → (y : ℍ[ℚ, a, b]) * x ∈ L)
    (hL_index : L.toAddSubgroup.relIndex Λ.toAddSubgroup = ℓ ^ 2) :
    ∃ c d : ↥Λ,
      (∃ y : ↥Λ, (c : ℍ[ℚ, a, b]) * (d : ℍ[ℚ, a, b]) - 1 = (m : ℚ) • (y : ℍ[ℚ, a, b])) ∧
      (∃ y : ↥Λ, (d : ℍ[ℚ, a, b]) * (c : ℍ[ℚ, a, b]) - 1 = (m : ℚ) • (y : ℍ[ℚ, a, b])) ∧
      (∀ x : ℍ[ℚ, a, b], x ∈ L₀ → x * (c : ℍ[ℚ, a, b]) ∈ L) ∧
      (∀ x : ℍ[ℚ, a, b], x ∈ L → x * (d : ℍ[ℚ, a, b]) ∈ L₀) := by sorry
