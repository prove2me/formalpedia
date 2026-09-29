-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_levelIdentity_of_not_dvd
-- name    : QuaternionAlgebra.IsEichlerOrder.levelIdentity_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/62d6888c-f04d-5e2b-8d6e-cd0ab4c6e541
-- title:
--   Level identity ℓ J' + Λ t = J't for ℓ ∤ N
-- statement:
--   Fix natural numbers $N, q, q'$ with $N$ nonzero and $q, q'$ prime, and assume $q \nmid N$, $q' \nmid N$ and $q' \neq q$. Let $a, b \in \mathbb{Q}$ be such that the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt`, i.e. $0 < a$ or $0 < b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the base change of $\mathbb{H}[\mathbb{Q},a,b]$ to the $v$-adic completion has all nonzero elements invertible precisely when $q \in v$ or $q' \in v$. Let $\Lambda$ be a $\mathbb{Z}$-submodule which is a maximal order (an order: containing $1$, closed under multiplication, with $\mathbb{Q}$-span everything and finitely generated, and maximal among such), let $N$ be squarefree, and let $R \leq \Lambda$ be an Eichler order of level $N$, i.e. $R = \Lambda_1 \cap \Lambda_2$ for maximal orders $\Lambda_1, \Lambda_2$ with $\Lambda_1 : R$ of relative index $N$. Let $J'$ be a $\mathbb{Z}$-submodule with $\Lambda \subseteq J'$, $\Lambda J' \subseteq J'$, $N J' \subseteq \Lambda$, relative index $N^2$ of $\Lambda$ in $J'$, and such that an element $x$ of $\Lambda$ lies in $R$ if and only if $J' x \subseteq J'$. Let $\ell$ be a prime not dividing $N$ and let $t \in R$ have reduced norm $\mathrm{nrd}(t) = \ell$, where $\mathrm{nrd}(x) = x_{\mathrm{re}}^2 - a x_{\mathrm{imI}}^2 - b x_{\mathrm{imJ}}^2 + ab\, x_{\mathrm{imK}}^2$. Then for every $x \in \mathbb{H}[\mathbb{Q},a,b]$ one has $x = \ell j + m t$ for some $j \in J'$, $m \in \Lambda$ if and only if $x = j t$ for some $j \in J'$; that is, $\ell J' + \Lambda t = J' t$.
--
--   This is the level identity used to compare the $\ell$-th Hecke operator with the action of a norm-$\ell$ element on the level module $J'$ attached to an Eichler order of squarefree level $N$, in the case $\ell \nmid N$. It feeds the analysis of Atkin–Lehner twists on Šimura curves arising from the indefinite quaternion algebra ramified exactly at $q$ and $q'$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsEichlerOrder_levelIdentity_of_not_dvd.lean

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

theorem QuaternionAlgebra.IsEichlerOrder.levelIdentity_of_not_dvd
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (hN : Squarefree N) (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (J' : Submodule ℤ ℍ[ℚ, a, b])
    (hJ' : Λ ≤ J' ∧ (∀ x ∈ Λ, ∀ y ∈ J', x * y ∈ J') ∧ (∀ y ∈ J', ((N : ℤ) • y) ∈ Λ) ∧
      Λ.toAddSubgroup.relIndex J'.toAddSubgroup = N ^ 2 ∧ (∀ x ∈ Λ, x ∈ R ↔ ∀ y ∈ J', y * x ∈ J'))
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (t : ℍ[ℚ, a, b]) (ht : t ∈ R) (hnt : nrd t = (ℓ : ℚ)) :
    (∀ x : ℍ[ℚ, a, b], (∃ j ∈ J', ∃ m ∈ Λ, (ℓ : ℤ) • j + m * t = x) ↔ ∃ j ∈ J', j * t = x) := by sorry
