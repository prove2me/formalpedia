-- Prove2me | Theorems.Thm_PadicInt_apply_sub_eq_smul_sub_of_idempotent_of_forall_sub_mem_of_forall_exists_pow_sub_smul
-- name    : PadicInt.apply_sub_eq_smul_sub_of_idempotent_of_forall_sub_mem_of_forall_exists_pow_sub_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/c5e61199-4787-5f6d-9017-f5877ba7a8d0
-- title:
--   Nakayama glue: inertia acts by χ on corner displacements
-- statement:
--   Let $p$ be a prime and let $T$ be a finitely generated module over $\mathbb{Z}_p$. Given an index type $\iota$, a subset $I \subseteq \iota$, a family of $\mathbb{Z}_p$-linear endomorphisms $\rho_g$ of $T$ indexed by $\iota$, a family of scalars $\chi_g \in \mathbb{Z}_p$, and three $\mathbb{Z}_p$-linear endomorphisms $e, U, V$ of $T$, assume: $e$ is idempotent ($e(e x) = e x$ for all $x$); $e$ commutes with $\rho_g$ for every $g \in I$, and $V$ commutes with $\rho_g$ for every $g \in I$; $e$ commutes with $U$ and with $V$; and $V(U(e x)) = e x$ for all $x$. Assume further that a submodule $T_0 \subseteq T$ is given such that $\rho_g x - x \in T_0$ for all $g \in I$ and all $x \in T$, and that for some $N \in \mathbb{N}$ every $y \in T_0$ admits a $z \in T_0$ with $\rho_g\bigl(U^N y - p z\bigr) = \chi_g \cdot \bigl(U^N y - p z\bigr)$ for all $g \in I$. The conclusion is that for all $g, h \in I$ and every $x \in T$ fixed by $e$ (that is, $e x = x$) one has $\rho_h(\rho_g x - x) = \chi_h \cdot (\rho_g x - x)$. No stability of $T_0$ under $e$, $U$ or $V$, and no torsion-freeness, is assumed.
--
--   This is the module-theoretic core of the existence half of the ordinary filtration: on the part of $T$ cut out by $e$, the displacements $\rho_g x - x$ produced by the group elements indexed by $I$ lie in the common $\chi$-eigenspace of the whole family. It is applied to the Tate module of a modular Jacobian, with $I$ an inertia subgroup, $\chi$ the cyclotomic character and $U, V$ the Hecke operator at $p$ together with its partial inverse on the ordinary corner, by [`ModularCurve.tateGaloisRep_smul_sub_eq_cyclotomicCharacter_smul_of_mem_inertiaSubgroupIn_cornerSubmodule_tateModule_jH_of_ordinary`](thm.html#ModularCurve.tateGaloisRep_smul_sub_eq_cyclotomicCharacter_smul_of_mem_inertiaSubgroupIn_cornerSubmodule_tateModule_jH_of_ordinary).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PadicInt_apply_sub_eq_smul_sub_of_idempotent_of_forall_sub_mem_of_forall_exists_pow_sub_smul.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PadicInt.apply_sub_eq_smul_sub_of_idempotent_of_forall_sub_mem_of_forall_exists_pow_sub_smul
    (p : ℕ) [Fact p.Prime] {T : Type*} [AddCommGroup T] [Module ℤ_[p] T] [Module.Finite ℤ_[p] T]
    {ι : Type*} (I : Set ι) (ρ : ι → T →ₗ[ℤ_[p]] T) (χ : ι → ℤ_[p])
    (e U V : T →ₗ[ℤ_[p]] T) (he : ∀ x, e (e x) = e x)
    (heρ : ∀ g ∈ I, ∀ x, e (ρ g x) = ρ g (e x)) (hVρ : ∀ g ∈ I, ∀ x, V (ρ g x) = ρ g (V x))
    (heU : ∀ x, e (U x) = U (e x)) (heV : ∀ x, e (V x) = V (e x)) (hVU : ∀ x, V (U (e x)) = e x)
    (T₀ : Submodule ℤ_[p] T)
    (hKUM : ∀ g ∈ I, ∀ x : T, ρ g x - x ∈ T₀)
    (hSLP : ∃ N : ℕ, ∀ y ∈ T₀, ∃ z ∈ T₀, ∀ g ∈ I,
      ρ g ((U ^ N) y - (p : ℤ_[p]) • z) = χ g • ((U ^ N) y - (p : ℤ_[p]) • z)) :
    ∀ g ∈ I, ∀ h ∈ I, ∀ x : T, e x = x → ρ h (ρ g x - x) = χ h • (ρ g x - x) := by sorry
