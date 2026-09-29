-- Prove2me | Theorems.Thm_Submodule_exists_finset_card_eq_finrank_forall_eq_zero_of_forall_exists_apply_ne_zero
-- name    : Submodule.exists_finset_card_eq_finrank_forall_eq_zero_of_forall_exists_apply_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/cf8db063-94b8-5e18-938e-3538c0484ba1
-- title:
--   Choosing dim D indices cutting out 0 in D
-- statement:
--   Let $k$ be a field, $V$ a $k$-vector space, $\iota$ an index type, and $(W_i)_{i\in\iota}$ a family of $k$-vector spaces; let $f_i \colon V \to W_i$ be $k$-linear maps, and let $D \subseteq V$ be a $k$-submodule that is finite-dimensional over $k$. Let $\mathrm{good} \subseteq \iota$ be a set of indices satisfying two conditions: first, for every finite subset $T \subseteq \iota$ there is some $i \in \mathrm{good}$ with $i \notin T$; second, for every $\psi \in D$ with $\psi \neq 0$ and every finite subset $T \subseteq \iota$ there is some $i \in \mathrm{good}$ with $i \notin T$ and $f_i(\psi) \neq 0$. Then for every finite subset $T_0 \subseteq \iota$ there exists a finite subset $Q \subseteq \iota$ with $Q \subseteq \mathrm{good}$, $Q$ disjoint from $T_0$, $\#Q = \dim_k D$, and such that every $\psi \in D$ with $f_i(\psi) = 0$ for all $i \in Q$ is zero; that is, $D \cap \bigcap_{i \in Q} \ker f_i = 0$.
--
--   This is the linear-algebra skeleton of the choice of auxiliary primes in the Taylor–Wiles method: $D$ plays the role of a dual Selmer group, the $f_i$ of restriction maps to decomposition groups at candidate primes, the first hypothesis of the availability of Taylor–Wiles primes outside any finite set, and the second of the Chebotarev argument annihilating no non-zero class. It is used in the construction of sets of Taylor–Wiles primes of cardinality the rank of the relevant first cohomology group, via [`ResidualGaloisRep.exists_taylorWilesPrimes_card_eq_finrank_continuousH1S_dualTwist`](thm.html#ResidualGaloisRep.exists_taylorWilesPrimes_card_eq_finrank_continuousH1S_dualTwist).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Submodule_exists_finset_card_eq_finrank_forall_eq_zero_of_forall_exists_apply_ne_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Submodule.exists_finset_card_eq_finrank_forall_eq_zero_of_forall_exists_apply_ne_zero
    {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
    {ι : Type*} {W : ι → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module k (W i)]
    (f : ∀ i, V →ₗ[k] W i) (D : Submodule k V) [FiniteDimensional k D]
    (good : Set ι)
    (hpad : ∀ T : Finset ι, ∃ i ∈ good, i ∉ T)
    (hkill : ∀ ψ ∈ D, ψ ≠ 0 → ∀ T : Finset ι, ∃ i ∈ good, i ∉ T ∧ f i ψ ≠ 0)
    (T₀ : Finset ι) :
    ∃ Q : Finset ι, ↑Q ⊆ good ∧ Disjoint Q T₀ ∧ Q.card = Module.finrank k D ∧
      ∀ ψ ∈ D, (∀ i ∈ Q, f i ψ = 0) → ψ = 0 := by sorry
