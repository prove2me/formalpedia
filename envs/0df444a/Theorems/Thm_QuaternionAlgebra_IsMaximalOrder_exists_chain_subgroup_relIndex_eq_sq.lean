-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_chain_subgroup_relIndex_eq_sq
-- name    : QuaternionAlgebra.IsMaximalOrder.exists_chain_subgroup_relIndex_eq_sq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/21cd8cbc-1e22-5e9f-b632-4383388bc2fe
-- title:
--   Filtration of a finite Λ-stable subgroup with square steps
-- statement:
--   Let $q$ and $q'$ be primes with $q' \ne q$, and let $a,b \in \mathbb{Q}$ be such that the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, that is: $a > 0$ or $b > 0$, and for every height-one prime $v$ of the ring of integers of $\mathbb{Q}$, every nonzero element of $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a unit precisely when $v$ contains $q$ or $q'$. Let $\Lambda$ be a $\mathbb{Z}$-submodule of $\mathbb{H}[\mathbb{Q},a,b]$ which is a maximal order: it contains $1$, is closed under multiplication, spans $\mathbb{H}[\mathbb{Q},a,b]$ over $\mathbb{Q}$, is finitely generated, and every order containing it equals it. Let $G$ be a commutative group and $\rho$ an assignment of a group endomorphism $\rho(x)$ of $G$ to each $x \in \Lambda$, such that $\rho(1)$ is the identity, $\rho(xy) = \rho(x) \circ \rho(y)$ for $x,y \in \Lambda$, and $\rho(x+y)(g) = \rho(x)(g)\,\rho(y)(g)$ for all $g \in G$. Let $N \le G$ be a subgroup whose underlying set is finite and which is stable under all $\rho(x)$, $x \in \Lambda$. Then there exist $e \in \mathbb{N}$, primes $\ell_0,\dots,\ell_{e-1}$ and subgroups $H_0,\dots,H_e$ of $G$ with $H_0 = \bot$, $H_e = N$, $H_j \le H_{j+1}$ for all $j$, each $H_j$ stable under every $\rho(x)$, the relative index of $H_j$ in $H_{j+1}$ equal to $\ell_j^2$, $g^{\ell_j} \in H_j$ for every $g \in H_{j+1}$, and, whenever $\ell_j \in \{q,q'\}$, $\rho(m)(g) \in H_j$ for every $g \in H_{j+1}$ and every $m \in \Lambda$ with $m\,\mathrm{star}(m)$ equal to the scalar $\ell_j k$ for some $k \in \mathbb{Z}$; moreover $\#N = \prod_{j} \ell_j^2$.
--
--   This is a Jordan–Hölder filtration of the finite $\Lambda$-module $N$ with its simple factors identified: each factor has order $\ell^2$ for a prime $\ell$, and at the two ramified primes $q,q'$ the factor is annihilated by the elements of $\Lambda$ of reduced norm divisible by $\ell$, i.e. by the two-sided prime above $\ell$. It feeds the construction of chains of level isogenies and Atkin–Lehner quotients of fake elliptic curves, and the associated statement producing injections of products of cyclic groups into torsion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsMaximalOrder_exists_chain_subgroup_relIndex_eq_sq.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open QuaternionAlgebra

theorem QuaternionAlgebra.IsMaximalOrder.exists_chain_subgroup_relIndex_eq_sq
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    {G : Type*} [CommGroup G] (ρ : ↥Λ → G →* G)
    (hρ_one : ∀ h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ, ρ ⟨1, h1⟩ = MonoidHom.id G)
    (hρ_mul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      ρ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = (ρ x).comp (ρ y))
    (hρ_add : ∀ (x y : ↥Λ) (g : G), ρ (x + y) g = ρ x g * ρ y g)
    (N : Subgroup G) (hN : (N : Set G).Finite) (hstab : ∀ (x : ↥Λ) (g : G), g ∈ N → ρ x g ∈ N) :
    ∃ (e : ℕ) (ℓ : Fin e → ℕ) (H : Fin (e + 1) → Subgroup G),
      (∀ j, (ℓ j).Prime) ∧ H 0 = ⊥ ∧ H (Fin.last e) = N ∧
      (∀ j : Fin e, H j.castSucc ≤ H j.succ) ∧
      (∀ (j : Fin (e + 1)) (x : ↥Λ) (g : G), g ∈ H j → ρ x g ∈ H j) ∧
      (∀ j : Fin e, (H j.castSucc).relIndex (H j.succ) = ℓ j ^ 2) ∧
      (∀ (j : Fin e) (g : G), g ∈ H j.succ → g ^ (ℓ j) ∈ H j.castSucc) ∧
      (∀ j : Fin e, (ℓ j = q ∨ ℓ j = q') → ∀ g : G, g ∈ H j.succ →
        ∀ (m : ↥Λ) (k : ℤ), (m : ℍ[ℚ, a, b]) * star (m : ℍ[ℚ, a, b]) = (((ℓ j : ℤ) * k : ℚ) : ℍ[ℚ, a, b]) →
          ρ m g ∈ H j.castSucc) ∧
      Nat.card N = ∏ j, ℓ j ^ 2 := by sorry
