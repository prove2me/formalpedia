-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_exists_nrd_eq_one_add_and_forall_smul_mul_eq_and_forall_mul_mul_eq_of_levelIdentity
-- name    : QuaternionAlgebra.IsEichlerOrder.exists_nrd_eq_one_add_and_forall_smul_mul_eq_and_forall_mul_mul_eq_of_levelIdentity
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/97162e6b-1249-5b5a-92bd-2b0318cb4b01
-- title:
--   Mod-ℓ unipotent element of Λ carrying Λ t to Λ t'
-- statement:
--   Fix natural numbers $N \neq 0$ and primes $q \neq q'$ with $q \nmid N$ and $q' \nmid N$, and rationals $a,b$ such that the quaternion algebra $B = \mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`: $a > 0$ or $b > 0$, and for each height-one prime $v$ of the ring of integers of $\mathbb{Q}$, every nonzero element of $B \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a unit precisely when $q \in v$ or $q' \in v$. Let $\Lambda \subseteq B$ be a $\mathbb{Z}$-submodule that is a maximal order, i.e. it contains $1$, is closed under multiplication, spans $B$ over $\mathbb{Q}$, is finitely generated, and is maximal among such submodules containing it; let $N$ be squarefree and let $R \subseteq \Lambda$ be an Eichler order of level $N$, meaning $R = \Lambda_1 \cap \Lambda_2$ for maximal orders $\Lambda_1, \Lambda_2$ with $[\Lambda_1 : R] = N$. Let $J'$ be a $\mathbb{Z}$-submodule with $\Lambda \subseteq J'$, $\Lambda J' \subseteq J'$, $N J' \subseteq \Lambda$, $[J' : \Lambda] = N^2$, and $R = \{x \in \Lambda : J' x \subseteq J'\}$. Let $\ell$ be a prime different from $q$ and $q'$, and let $t, t' \in \Lambda$ have reduced norm $\ell$ and satisfy the level identities $\ell J' + \Lambda t = J' t$ and $\ell J' + \Lambda t' = J' t'$ (as equalities of subsets of $B$, stated elementwise). Then there exists $c \in \Lambda$ such that $\operatorname{nrd}(c) = 1 + \ell k$ for some integer $k$, such that every $y \in J'$ satisfies $(Ny)c = Ny'' + \ell z$ for some $y'' \in J'$ and $z \in \Lambda$, and such that every $m \in \Lambda$ satisfies $mtc = m't' + \ell z$ for some $m', z \in \Lambda$.
--
--   This is the purely local step at $\ell$ in the proof that the reduced-norm-one units of an Eichler order act transitively on the $\Lambda$-lines transversal to the level at $\ell$: working in $\Lambda/\ell\Lambda \cong M_2(\mathbb{F}_\ell)$, it produces an element of $\Lambda$ that is unipotent modulo $\ell$, stabilises the level module $NJ'$ modulo $\ell\Lambda$, and moves $\Lambda t$ into $\Lambda t'$ modulo $\ell\Lambda$. It is used by [`QuaternionAlgebra.IsEichlerOrder.exists_nrd_eq_levelIdentity_and_forall_exists_isUnitOf_nrd_eq_one_mul_mul_iff_of_levelIdentity`](thm.html#QuaternionAlgebra.IsEichlerOrder.exists_nrd_eq_levelIdentity_and_forall_exists_isUnitOf_nrd_eq_one_mul_mul_iff_of_levelIdentity), where it is combined with congruence and approximation arguments to the full modulus.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsEichlerOrder_exists_nrd_eq_one_add_and_forall_smul_mul_eq_and_forall_mul_mul_eq_of_levelIdentity.lean

import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion MatrixGroups Pointwise
open QuaternionAlgebra
open CerednikDrinfeld

theorem QuaternionAlgebra.IsEichlerOrder.exists_nrd_eq_one_add_and_forall_smul_mul_eq_and_forall_mul_mul_eq_of_levelIdentity
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (hN : Squarefree N) (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (J' : Submodule ℤ ℍ[ℚ, a, b])
    (hJ' : Λ ≤ J' ∧ (∀ x ∈ Λ, ∀ y ∈ J', x * y ∈ J') ∧ (∀ y ∈ J', ((N : ℤ) • y) ∈ Λ) ∧
      Λ.toAddSubgroup.relIndex J'.toAddSubgroup = N ^ 2 ∧ (∀ x ∈ Λ, x ∈ R ↔ ∀ y ∈ J', y * x ∈ J'))
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q')
    (t t' : ℍ[ℚ, a, b]) (ht : t ∈ Λ) (ht' : t' ∈ Λ) (hnt : nrd t = (ℓ : ℚ)) (hnt' : nrd t' = (ℓ : ℚ))
    (hlev : ∀ x : ℍ[ℚ, a, b], (∃ j ∈ J', ∃ m ∈ Λ, (ℓ : ℤ) • j + m * t = x) ↔ ∃ j ∈ J', j * t = x)
    (hlev' : ∀ x : ℍ[ℚ, a, b], (∃ j ∈ J', ∃ m ∈ Λ, (ℓ : ℤ) • j + m * t' = x) ↔ ∃ j ∈ J', j * t' = x) :
    ∃ c ∈ Λ, (∃ k : ℤ, nrd c = 1 + (ℓ : ℚ) * (k : ℚ)) ∧
      (∀ y ∈ J', ∃ y'' ∈ J', ∃ z ∈ Λ, ((N : ℤ) • y) * c = (N : ℤ) • y'' + (ℓ : ℤ) • z) ∧
      (∀ m ∈ Λ, ∃ m' ∈ Λ, ∃ z ∈ Λ, m * t * c = m' * t' + (ℓ : ℤ) • z) := by sorry
