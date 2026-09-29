-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_forall_mul_star_mem_imp_mem_iff_not_conj_eq_and_not_conj_le_of_dvd
-- name    : QuaternionAlgebra.IsEichlerOrder.forall_mul_star_mem_imp_mem_iff_not_conj_eq_and_not_conj_le_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/457aa7b5-138c-5ff5-bbcc-76dd9250df49
-- title:
--   Transversality of a norm-ℓ element at ℓ ∣ N
-- statement:
--   Fix natural numbers $N, q, q'$ with $N \neq 0$, $q$ and $q'$ prime, $q \nmid N$, $q' \nmid N$ and $q' \neq q$, and rationals $a, b$ such that the quaternion algebra $B = \mathbb{H}[\mathbb{Q}, a, b]$ satisfies the project's condition `IsIndefiniteRamifiedExactlyAt`: $0 < a$ or $0 < b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the completion $B \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a division algebra exactly when $v$ contains $q$ or $q'$. Let $\Lambda \subseteq B$ be a $\mathbb{Z}$-submodule which is a maximal order (containing $1$, closed under multiplication, finitely generated, spanning $B$ over $\mathbb{Q}$, and maximal among such), let $N$ be squarefree, and let $R \le \Lambda$ be an Eichler order of level $N$ in the project's sense, i.e. $R = \Lambda_1 \cap \Lambda_2$ for maximal orders $\Lambda_i$ with the relative index of $R$ in $\Lambda_1$ equal to $N$. Let $J'$ be a $\mathbb{Z}$-submodule with $\Lambda \le J'$, $\Lambda J' \subseteq J'$, $N J' \subseteq \Lambda$, relative index of $\Lambda$ in $J'$ equal to $N^2$, and such that for $x \in \Lambda$ one has $x \in R$ iff $J' x \subseteq J'$. Let $w \in B^\times$ lie in $R$ with $\mathrm{nrd}\, w = N$ and satisfy $x \in R \iff w x w^{-1} \in R$ for all $x \in B$. Finally let $\ell$ be a prime dividing $N$, let $t \in R$ have $\mathrm{nrd}\, t = \ell$, and let $T \in B^\times$ be a unit with underlying element $t$. Writing $x = w T w^{-1}$, the conclusion is the equivalence: every $j \in J'$ with $j \bar t \in \Lambda$ already lies in $\Lambda$, if and only if both $x^{-1} z x \in R \iff z \in R$ fails for some $z \in B$, and $x^{-1} r x \in \Lambda$ fails for some $r \in R$.
--
--   This is the local statement at a prime $\ell$ dividing the level $N$ underlying the dictionary between Hecke correspondences on a Shimura curve and double cosets: it converts the transversality condition on a norm-$\ell$ element $t$ of the Eichler order into two conditions on the Atkin–Lehner conjugate $w T w^{-1}$, namely that conjugation by it neither preserves $R$ nor carries $R$ into the maximal order $\Lambda$. It is used in the proof of [`QuaternionAlgebra.IsEichlerOrder.levelIdentity_iff_not_conj_eq_and_not_conj_le_of_dvd`](thm.html#QuaternionAlgebra.IsEichlerOrder.levelIdentity_iff_not_conj_eq_and_not_conj_le_of_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsEichlerOrder_forall_mul_star_mem_imp_mem_iff_not_conj_eq_and_not_conj_le_of_dvd.lean

import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_ClassSetGraph

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion TensorProduct NumberField MatrixGroups Pointwise
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

theorem QuaternionAlgebra.IsEichlerOrder.forall_mul_star_mem_imp_mem_iff_not_conj_eq_and_not_conj_le_of_dvd
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (hN : Squarefree N) (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (J' : Submodule ℤ ℍ[ℚ, a, b])
    (hJ' : Λ ≤ J' ∧ (∀ x ∈ Λ, ∀ y ∈ J', x * y ∈ J') ∧ (∀ y ∈ J', ((N : ℤ) • y) ∈ Λ) ∧
      Λ.toAddSubgroup.relIndex J'.toAddSubgroup = N ^ 2 ∧ (∀ x ∈ Λ, x ∈ R ↔ ∀ y ∈ J', y * x ∈ J'))
    (w : (ℍ[ℚ, a, b])ˣ) (hwR : (w : ℍ[ℚ, a, b]) ∈ R) (hwn : nrd (w : ℍ[ℚ, a, b]) = (N : ℚ))
    (hwnorm : ∀ x : ℍ[ℚ, a, b], x ∈ R ↔ (w : ℍ[ℚ, a, b]) * x * ((w⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ∈ R)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ℓ ∣ N) (t : ℍ[ℚ, a, b]) (ht : t ∈ R) (hnt : nrd t = (ℓ : ℚ))
    (T : (ℍ[ℚ, a, b])ˣ) (hT : (T : ℍ[ℚ, a, b]) = t) :
    (∀ j ∈ J', j * star t ∈ Λ → j ∈ Λ) ↔
      ((¬ ∀ z : ℍ[ℚ, a, b],
          (((w * T * w⁻¹)⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * z * ((w * T * w⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ∈ R ↔ z ∈ R) ∧
        (¬ ∀ r ∈ R,
          (((w * T * w⁻¹)⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * r * ((w * T * w⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ∈ Λ)) := by sorry
