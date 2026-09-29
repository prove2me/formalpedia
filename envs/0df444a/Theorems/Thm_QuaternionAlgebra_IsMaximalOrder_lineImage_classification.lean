-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_lineImage_classification
-- name    : QuaternionAlgebra.IsMaximalOrder.lineImage_classification
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/2e81f1e9-d952-5e20-b733-f121dced949b
-- title:
--   Line images in a rank-one Λ/ℓΛ-module
-- statement:
--   Let $B=\mathbb H[\mathbb Q,a,b]$ for rationals $a,b$, let $q,q'$ be primes with $q'\neq q$, and assume `IsIndefiniteRamifiedExactlyAt a b q q'`: $0<a$ or $0<b$, and for every height-one prime $v$ of $\mathcal O_{\mathbb Q}$ the algebra $B\otimes_{\mathbb Q}\mathbb Q_v$ has all nonzero elements invertible exactly when $q\in v$ or $q'\in v$. Let $\Lambda\subseteq B$ be a $\mathbb Z$-submodule that is an order (containing $1$, closed under multiplication, $\mathbb Q$-spanning $B$, finitely generated) and is maximal among orders for inclusion, and let $\ell$ be a prime with $\ell\neq q,q'$. Let $M$ be an abelian group together with $\rho$ assigning to each $m\in\Lambda$ an endomorphism of $M$, subject to $\rho(1)=\mathrm{id}$, $\rho(xy)=\rho(x)\circ\rho(y)$ and additivity in $m$, and let $P_0\in M$ be such that every $P\in M$ equals $\rho(m)P_0$ for some $m\in\Lambda$, while $\rho(m)P_0=0$ iff $m=\ell m'$ in $B$ for some $m'\in\Lambda$. Call a $\mathbb Z$-submodule $J\subseteq B$ a proper line if $J\le\Lambda$, $\ell\cdot\Lambda\subseteq J$, $\Lambda J\subseteq J$, $J\not\subseteq\ell\cdot\Lambda$ and $J\neq\Lambda$, and put $S_J=\{\rho(m)P_0: m\in\Lambda,\ m\in J\}$. The conclusion is fourfold: for each proper line $J$ there is an additive bijection $(\mathbb Z/\ell)^2\to S_J$ and $S_J$ is stable under every $\rho(n)$, $n\in\Lambda$; for distinct proper lines $J\neq J'$, any $P$ in both $S_J$ and $S_{J'}$ is $0$; every $\rho$-stable additive subgroup $S\le M$ admitting an additive bijection with $(\mathbb Z/\ell)^2$ equals $S_J$ for exactly one proper line $J$; and for every $\rho$-stable additive subgroup $T\le M$ and every proper line $J$, either $S_J\cap T=0$ or $S_J\subseteq T$.
--
--   This is the algebraic classification, over $\Lambda/\ell\Lambda\cong M_2(\mathbb F_\ell)$, of the $\Lambda$-stable subgroups of type $(\mathbb Z/\ell)^2$ in a module that is free of rank one modulo $\ell$: they correspond bijectively to the $\ell+1$ proper left $\Lambda$-lines modulo $\ell$, pairwise meeting in $0$, and each is either met trivially by or contained in any stable subgroup. It is used in the enumeration of extra level structures on fake elliptic curves, via [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_enum`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_enum), the module structure hypotheses being those delivered for $\ell$-torsion of an abelian surface with quaternionic multiplication. The proof cites [`QuaternionAlgebra.exists_linearMap_matrix_zmod_of_isMaximalOrder_of_ne`](thm.html#QuaternionAlgebra.exists_linearMap_matrix_zmod_of_isMaximalOrder_of_ne) and [`QuaternionAlgebra.IsMaximalOrder.natCard_properLine_eq_and_inf_eq`](thm.html#QuaternionAlgebra.IsMaximalOrder.natCard_properLine_eq_and_inf_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsMaximalOrder_lineImage_classification.lean

import Definitions.Def_CerednikDrinfeld_QMModuliProps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry
open QuaternionAlgebra
open CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem QuaternionAlgebra.IsMaximalOrder.lineImage_classification
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q')
    (M : Type) [AddCommGroup M] (ρ : ↥Λ → M →+ M)
    (ρ_one : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, ρ ⟨1, h⟩ = AddMonoidHom.id M)
    (ρ_mul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      ρ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = (ρ x).comp (ρ y))
    (ρ_add : ∀ x y : ↥Λ, ρ (x + y) = ρ x + ρ y)
    (P₀ : M) (hgen : ∀ P : M, ∃ m : ↥Λ, P = ρ m P₀)
    (hann : ∀ m : ↥Λ, ρ m P₀ = 0 ↔ ∃ m' : ↥Λ, (m : ℍ[ℚ, a, b]) = ((ℓ : ℚ) : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b])) :

    (∀ J : Submodule ℤ ℍ[ℚ, a, b], (J ≤ Λ ∧ (∀ y ∈ Λ, (ℓ : ℤ) • y ∈ J) ∧ (∀ m ∈ Λ, ∀ x ∈ J, m * x ∈ J) ∧
          (∃ x ∈ J, ¬ ∃ y ∈ Λ, x = (ℓ : ℤ) • y) ∧ J ≠ Λ) →
      (∃ e : ZMod ℓ × ZMod ℓ ≃ {P : M // (∃ m : ↥Λ, (m : ℍ[ℚ, a, b]) ∈ J ∧ P = ρ m P₀)},
          ∀ x y : ZMod ℓ × ZMod ℓ, ((e (x + y) : {P : M // (∃ m : ↥Λ, (m : ℍ[ℚ, a, b]) ∈ J ∧ P = ρ m P₀)}) : M) = (e x : M) + (e y : M)) ∧
      (∀ (n : ↥Λ) (P : M), (∃ m : ↥Λ, (m : ℍ[ℚ, a, b]) ∈ J ∧ P = ρ m P₀) → (∃ m : ↥Λ, (m : ℍ[ℚ, a, b]) ∈ J ∧ ρ n P = ρ m P₀))) ∧

    (∀ J J' : Submodule ℤ ℍ[ℚ, a, b], (J ≤ Λ ∧ (∀ y ∈ Λ, (ℓ : ℤ) • y ∈ J) ∧ (∀ m ∈ Λ, ∀ x ∈ J, m * x ∈ J) ∧
          (∃ x ∈ J, ¬ ∃ y ∈ Λ, x = (ℓ : ℤ) • y) ∧ J ≠ Λ) → (J' ≤ Λ ∧ (∀ y ∈ Λ, (ℓ : ℤ) • y ∈ J') ∧ (∀ m ∈ Λ, ∀ x ∈ J', m * x ∈ J') ∧
          (∃ x ∈ J', ¬ ∃ y ∈ Λ, x = (ℓ : ℤ) • y) ∧ J' ≠ Λ) → J ≠ J' →
      ∀ P : M, (∃ m : ↥Λ, (m : ℍ[ℚ, a, b]) ∈ J ∧ P = ρ m P₀) → (∃ m : ↥Λ, (m : ℍ[ℚ, a, b]) ∈ J' ∧ P = ρ m P₀) → P = 0) ∧

    (∀ S : AddSubgroup M, (∀ (n : ↥Λ) (P : M), P ∈ S → ρ n P ∈ S) →
      (∃ e : ZMod ℓ × ZMod ℓ ≃ S, ∀ x y : ZMod ℓ × ZMod ℓ, ((e (x + y) : S) : M) = (e x : M) + (e y : M)) →
      ∃! J : Submodule ℤ ℍ[ℚ, a, b], (J ≤ Λ ∧ (∀ y ∈ Λ, (ℓ : ℤ) • y ∈ J) ∧ (∀ m ∈ Λ, ∀ x ∈ J, m * x ∈ J) ∧
          (∃ x ∈ J, ¬ ∃ y ∈ Λ, x = (ℓ : ℤ) • y) ∧ J ≠ Λ) ∧ ∀ P : M, P ∈ S ↔ (∃ m : ↥Λ, (m : ℍ[ℚ, a, b]) ∈ J ∧ P = ρ m P₀)) ∧

    (∀ T : AddSubgroup M, (∀ (n : ↥Λ) (P : M), P ∈ T → ρ n P ∈ T) →
      ∀ J : Submodule ℤ ℍ[ℚ, a, b], (J ≤ Λ ∧ (∀ y ∈ Λ, (ℓ : ℤ) • y ∈ J) ∧ (∀ m ∈ Λ, ∀ x ∈ J, m * x ∈ J) ∧
          (∃ x ∈ J, ¬ ∃ y ∈ Λ, x = (ℓ : ℤ) • y) ∧ J ≠ Λ) →
        (∀ P : M, (∃ m : ↥Λ, (m : ℍ[ℚ, a, b]) ∈ J ∧ P = ρ m P₀) → P ∈ T → P = 0) ∨ (∀ P : M, (∃ m : ↥Λ, (m : ℍ[ℚ, a, b]) ∈ J ∧ P = ρ m P₀) → P ∈ T)) := by sorry
