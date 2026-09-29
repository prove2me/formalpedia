-- Prove2me | Theorems.Thm_Subgroup_exists_exact_fundamental_domain_of_secondCountableTopology
-- name    : Subgroup.exists_exact_fundamental_domain_of_secondCountableTopology
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/8e5926e0-c187-5a69-9146-bb7197d94012
-- title:
--   Exact fundamental domain for a discrete subgroup
-- statement:
--   Let $G$ be a group carrying a topology making it a topological group whose topology is second countable, and let $\Gamma$ be a subgroup of $G$. Assume $\Gamma$ is discrete in the following sense: there is an open set $V \subseteq G$ with $V \cap \Gamma = \{1\}$, i.e. $1$ is isolated in $\Gamma$ in the strong form that the intersection of $V$ with the underlying set of $\Gamma$ is exactly the singleton $\{1\}$. Then there exists a set $F \subseteq G$ with two properties. First, $F$ is a countable union of differences of open sets: there are families $U, C : \mathbb{N} \to \mathrm{Set}\,G$ with every $U_n$ open, every $C_n$ open, and $F = \bigcup_{n} (U_n \setminus C_n)$. Second, $F$ is an exact transversal for the action of $\Gamma$ on $G$ by left translation: for every $x \in G$ there is exactly one $\gamma \in \Gamma$ with $\gamma x \in F$.
--
--   This is the classical existence of a Borel fundamental domain (an exact Borel transversal) for the left translation action of a discrete subgroup on a second-countable topological group, with the Borel condition made explicit in the concrete form of a countable union of differences of open sets. It is used in the project to produce fundamental domains for integration: for the principal ideles inside the ideles of a number field in the global Tate theory, and in the construction of slab domains and of integrals of automorphic forms over quotients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Subgroup_exists_exact_fundamental_domain_of_secondCountableTopology.lean

import Mathlib.Topology.Algebra.Group.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Subgroup.exists_exact_fundamental_domain_of_secondCountableTopology
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    (Γ : Subgroup G) (hdisc : ∃ V : Set G, IsOpen V ∧ V ∩ (Γ : Set G) = {1}) :
    ∃ F : Set G,
      (∃ U C : ℕ → Set G, (∀ n, IsOpen (U n)) ∧ (∀ n, IsOpen (C n)) ∧ F = ⋃ n, U n \ C n) ∧
      ∀ x : G, ∃! γ : ↥Γ, (γ : G) * x ∈ F := by sorry
