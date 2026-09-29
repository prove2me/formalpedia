-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_exists_nrd_eq_levelIdentity_and_forall_exists_isUnitOf_nrd_eq_one_mul_mul_iff_of_levelIdentity
-- name    : QuaternionAlgebra.IsEichlerOrder.exists_nrd_eq_levelIdentity_and_forall_exists_isUnitOf_nrd_eq_one_mul_mul_iff_of_levelIdentity
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/c7181006-9266-590a-83dd-a62e819b1730
-- title:
--   Transversal norm-ℓ elements of an Eichler order, up to norm-one units
-- statement:
--   Fix natural numbers $N \neq 0$ and primes $q, q'$ with $q' \neq q$, neither dividing $N$, and rationals $a, b$ such that the quaternion algebra $B = \mathbb{H}[\mathbb{Q}, a, b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $0 < a$ or $0 < b$, and for every height-one prime $v$ of the integers of $\mathbb{Q}$ every nonzero element of $B \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a unit exactly when $v$ contains $q$ or $q'$. Let $\Lambda \subseteq B$ be a $\mathbb{Z}$-submodule that is a maximal order (it contains $1$, is closed under multiplication, is finitely generated, spans $B$ over $\mathbb{Q}$, and every order containing it equals it), let $N$ be squarefree, and let $R \subseteq \Lambda$ be an Eichler order of level $N$, that is, $R = \Lambda_1 \cap \Lambda_2$ for maximal orders $\Lambda_i$ with the additive index of $R$ in $\Lambda_1$ equal to $N$. Let $J' \subseteq B$ be a $\mathbb{Z}$-submodule with $\Lambda \subseteq J'$, $\Lambda J' \subseteq J'$, $N J' \subseteq \Lambda$, additive index of $\Lambda$ in $J'$ equal to $N^2$, and such that for $x \in \Lambda$ one has $x \in R$ iff $J' x \subseteq J'$. Let $\ell$ be a prime different from $q$ and $q'$. Call $t$ transversal when $\ell J' + \Lambda t = J' t$ (stated elementwise in both directions). The conclusion is twofold: first, there exists $t \in R$ with $\mathrm{nrd}\, t = \ell$ (the reduced norm being $t_{re}^2 - a t_{imI}^2 - b t_{imJ}^2 + ab\, t_{imK}^2$) which is transversal; second, for any two transversal $t, t' \in R$ of reduced norm $\ell$ there is $u \in B$ lying in $R$ with a two-sided inverse in $R$, with $\mathrm{nrd}\, u = 1$, and with $\Lambda(tu) = \Lambda t'$ as subsets of $B$.
--
--   This is the arithmetic input of Eichler's theory behind the single-orbit statement that the norm-one units of an Eichler order act transitively on the $\Lambda$-lines of reduced norm $\ell$ transversal to the level module, so that the corresponding double coset space is a single point. It is used in the study of the coarse moduli interpretation of the Čerednik–Drinfeld setting, in the proof of integrality at $\ell$ over the complex points for squarefree level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsEichlerOrder_exists_nrd_eq_levelIdentity_and_forall_exists_isUnitOf_nrd_eq_one_mul_mul_iff_of_levelIdentity.lean

import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion MatrixGroups Pointwise
open QuaternionAlgebra CerednikDrinfeld

theorem QuaternionAlgebra.IsEichlerOrder.exists_nrd_eq_levelIdentity_and_forall_exists_isUnitOf_nrd_eq_one_mul_mul_iff_of_levelIdentity
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (hN : Squarefree N) (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (J' : Submodule ℤ ℍ[ℚ, a, b])
    (hJ' : Λ ≤ J' ∧ (∀ x ∈ Λ, ∀ y ∈ J', x * y ∈ J') ∧ (∀ y ∈ J', ((N : ℤ) • y) ∈ Λ) ∧
      Λ.toAddSubgroup.relIndex J'.toAddSubgroup = N ^ 2 ∧ (∀ x ∈ Λ, x ∈ R ↔ ∀ y ∈ J', y * x ∈ J'))
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q') :

    (∃ t ∈ R, nrd t = (ℓ : ℚ) ∧
      (∀ x : ℍ[ℚ, a, b], (∃ j ∈ J', ∃ m ∈ Λ, (ℓ : ℤ) • j + m * t = x) ↔ ∃ j ∈ J', j * t = x)) ∧

    (∀ t t' : ℍ[ℚ, a, b], t ∈ R → t' ∈ R → nrd t = (ℓ : ℚ) → nrd t' = (ℓ : ℚ) →
      (∀ x : ℍ[ℚ, a, b], (∃ j ∈ J', ∃ m ∈ Λ, (ℓ : ℤ) • j + m * t = x) ↔ ∃ j ∈ J', j * t = x) →
      (∀ x : ℍ[ℚ, a, b], (∃ j ∈ J', ∃ m ∈ Λ, (ℓ : ℤ) • j + m * t' = x) ↔ ∃ j ∈ J', j * t' = x) →
      ∃ u : ℍ[ℚ, a, b], IsUnitOf R u ∧ nrd u = 1 ∧
        ∀ x : ℍ[ℚ, a, b], (∃ m ∈ Λ, m * (t * u) = x) ↔ ∃ m ∈ Λ, m * t' = x) := by sorry
