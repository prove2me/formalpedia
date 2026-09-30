-- Prove2me | Theorems.Thm_PhilipponMultiplicity_analytic_subgroup_containment_of_local_containment
-- name    : PhilipponMultiplicity.analytic_subgroup_containment_of_local_containment
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-25T21:36:49.926658+00:00
-- url     : https://prove2.me/theorems/daefbe35-87b6-4029-8fc9-b777fb365f40
-- title:
--   Local analytic-subgroup containment extends across the convergence ball
-- statement:
--   Let $K$ be a complete nontrivially normed field, $G$ an embedded product of commutative algebraic groups, $A$ a local analytic group homomorphism with homogeneous coordinate series converging throughout its specified parameter ball, and $H$ a closed algebraic subgroup of $G$. If the local image of $A$ lies in $H$ near the origin, then
--   $$
--   \langle\operatorname{im}A\rangle\subseteq H.
--   $$
--   The conclusion includes the entire original parameter ball, not merely a smaller neighborhood. No connectedness assumption on that ball or restriction to archimedean fields is made.
-- source:
--   Philippon (1986), Lemmes de zéros dans les groupes algébriques commutatifs, https://numdam.org/articles/10.24033/bsmf.2060/, §2 p. 358 and §4 pp. 377–378, the analytic-subgroup/tangent-space factorization preceding Lemma 4.6. Granular analytic foundation for that step, not an additional numbered paper theorem.

import Definitions.Def_PhilipponMultiplicity_Analytic
set_option autoImplicit false
open scoped BigOperators Topology
open Filter PhilipponMultiplicity

theorem PhilipponMultiplicity.analytic_subgroup_containment_of_local_containment
    (K : Type*) [NontriviallyNormedField K] [CompleteSpace K]
    (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G) (H : AlgebraicSubgroup G)
    (hlocal : ∀ᶠ z in 𝓝 (0 : A.ParameterSpace),
      ∀ hz : z ∈ A.domain, A.map ⟨z, hz⟩ ∈ H.carrier) :
    A.carrier ⊆ H.carrier := by sorry
