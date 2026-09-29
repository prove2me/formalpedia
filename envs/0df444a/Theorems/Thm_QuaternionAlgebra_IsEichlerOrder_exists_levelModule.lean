-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_exists_levelModule
-- name    : QuaternionAlgebra.IsEichlerOrder.exists_levelModule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/f4303bc9-226b-5bae-88b3-33f705496110
-- title:
--   Level module attached to an Eichler order in a maximal order
-- statement:
--   Let $N,q,q'$ be natural numbers with $N \neq 0$ and $q,q'$ prime, assume $q \nmid N$, $q' \nmid N$ and $q' \neq q$, and let $a,b$ be rationals such that the quaternion algebra $B = \mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt`: $0 < a$ or $0 < b$, and for every height-one prime $v$ of the ring of integers of $\mathbb{Q}$, every nonzero element of $B \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a unit precisely when $v$ contains $q$ or $q'$. Let $\Lambda \subseteq B$ be a $\mathbb{Z}$-submodule which is a maximal order, i.e. it contains $1$, is multiplicatively closed, spans $B$ over $\mathbb{Q}$, is finitely generated, and is the only order containing it; let $N$ be squarefree and let $R \subseteq \Lambda$ be a $\mathbb{Z}$-submodule which is an Eichler order of level $N$, i.e. $R = \Lambda_1 \cap \Lambda_2$ for maximal orders $\Lambda_1,\Lambda_2$ with $[\Lambda_1 : R] = N$. Finally let $\iota : B \to M_2(\mathbb{R})$ be an injective $\mathbb{Q}$-algebra homomorphism. Then there exists a $\mathbb{Z}$-submodule $J' \subseteq B$ with $\Lambda \subseteq J'$, with $\Lambda J' \subseteq J'$, with $N y \in \Lambda$ for all $y \in J'$, with $[J' : \Lambda] = N^2$ (the index of $\Lambda$ relative to $J'$ as additive subgroups), and such that an element $x \in \Lambda$ lies in $R$ if and only if $J' x \subseteq J'$.
--
--   The submodule $J'$ is the 'level module' of the Eichler order $R$ of level $N$ inside the maximal order $\Lambda$: locally away from $N$ it is $\Lambda$, while at $\ell \mid N$ it is the superlattice of index $\ell^2$ whose right stabiliser in $\Lambda$ cuts out $R$. It is used in the Čerednik–Drinfeld part of the development, where period lattices $\iota(\Lambda)\binom{\tau}{1}$ and their $N^2$-index superlattices $\iota(J')\binom{\tau}{1}$ describe level structures on the quaternionic Shimura curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsEichlerOrder_exists_levelModule.lean

import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion MatrixGroups Pointwise
open QuaternionAlgebra CerednikDrinfeld

theorem QuaternionAlgebra.IsEichlerOrder.exists_levelModule
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (hN : Squarefree N) (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι) :
    ∃ J' : Submodule ℤ ℍ[ℚ, a, b], Λ ≤ J' ∧ (∀ x ∈ Λ, ∀ y ∈ J', x * y ∈ J') ∧ (∀ y ∈ J', ((N : ℤ) • y) ∈ Λ) ∧
      Λ.toAddSubgroup.relIndex J'.toAddSubgroup = N ^ 2 ∧ (∀ x ∈ Λ, x ∈ R ↔ ∀ y ∈ J', y * x ∈ J') := by sorry
