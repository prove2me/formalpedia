-- Prove2me | Theorems.Thm_Representation_nonempty_equiv_torsionBy_quotient_of_coprime
-- name    : Representation.nonempty_equiv_torsionBy_quotient_of_coprime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/e1aabbe4-f655-575b-8c52-4f207fd5021b
-- title:
--   A[p] ≅ A/pA as G-modules when p ∤ #G
-- statement:
--   Let $G$ be a finite group, $p$ a prime, and suppose the cardinality of $G$ is coprime to $p$. Let $A$ be a finite abelian group, regarded as a $\mathbb{Z}$-module, and let $\rho$ be a $\mathbb{Z}$-linear representation of $G$ on $A$. Two invariance hypotheses are imposed: for every $g \in G$, the $p$-torsion submodule $A[p] = \{a : p a = 0\}$ is contained in its preimage under $\rho(g)$, and likewise the submodule $p A = p \cdot \top$ is contained in its preimage under $\rho(g)$; that is, both $A[p]$ and $pA$ are stable under the action of each group element. Under these assumptions the conclusion asserts that the type of isomorphisms of representations between the subrepresentation of $\rho$ carried by $A[p]$ and the quotient representation of $\rho$ on $A / pA$ is nonempty, i.e. these two $G$-modules are isomorphic, without a specific isomorphism being exhibited.
--
--   This is the standard comparison of $p$-torsion and $p$-cokernel for a finite module over a finite group of order prime to $p$: over the semisimple ring $\mathbb{F}_p[G]$ the class $[A[p]] - [A/pA]$ is additive in short exact sequences and vanishes on simple modules, so the two modules coincide up to isomorphism. It serves as the base case for dévissage arguments computing Euler characteristics of finite Galois modules, and is cited by [`NumberField.LevelArith.nonempty_repTorsionP_iso_repModP`](thm.html#NumberField.LevelArith.nonempty_repTorsionP_iso_repModP).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Representation_nonempty_equiv_torsionBy_quotient_of_coprime.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory MonoidalCategory Module
open scoped Classical TensorProduct Pointwise

theorem Representation.nonempty_equiv_torsionBy_quotient_of_coprime
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hG : (Nat.card G).Coprime p)
    {A : Type} [AddCommGroup A] [Finite A] (ρ : Representation ℤ G A)
    (h1 : ∀ g, Submodule.torsionBy ℤ A (p : ℤ) ≤ (Submodule.torsionBy ℤ A (p : ℤ)).comap (ρ g))
    (h2 : ∀ g, (p : ℤ) • (⊤ : Submodule ℤ A) ≤ ((p : ℤ) • (⊤ : Submodule ℤ A)).comap (ρ g)) :
    Nonempty ((ρ.subrepresentation _ h1).Equiv (ρ.quotient _ h2)) := by sorry
