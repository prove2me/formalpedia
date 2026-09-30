-- Prove2me | Theorems.Thm_PhilipponMultiplicity_analytic_subgroup_local_containment_of_tangent
-- name    : PhilipponMultiplicity.analytic_subgroup_local_containment_of_tangent
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-25T21:36:53.934682+00:00
-- url     : https://prove2.me/theorems/3fa2e504-9521-443d-87a5-f0c2e602f706
-- title:
--   Tangent containment implies local analytic-subgroup containment
-- statement:
--   Let $K$ be isometrically isomorphic to $\mathbb C$ or to a p-adic complex field. Let $A$ be a local analytic group homomorphism into an embedded product $G$ of commutative algebraic groups, and let $H$ be an algebraic subgroup. Suppose every parameter direction is annihilated by the differential at the identity of every equation in the actual vanishing ideal of $H$:
--   $$
--   \ker_T(I(H)\circ A)=K^d.
--   $$
--   Then there is a neighborhood of the parameter origin on which
--   $$
--   A(z)\in H.
--   $$
--   This is the local geometric implication supplied by the Lie/exponential factorization in the paper. It makes no claim about the rest of the prescribed convergence ball.
-- source:
--   Philippon (1986), Lemmes de zéros dans les groupes algébriques commutatifs, https://numdam.org/articles/10.24033/bsmf.2060/, §2 p. 358 and §4 pp. 377–378, the analytic-subgroup/tangent-space factorization preceding Lemma 4.6. Granular analytic foundation for that step, not an additional numbered paper theorem.

import Definitions.Def_PhilipponMultiplicity_Analytic
set_option autoImplicit false
open scoped BigOperators Topology
open Filter PhilipponMultiplicity

theorem PhilipponMultiplicity.analytic_subgroup_local_containment_of_tangent
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G) (H : AlgebraicSubgroup G)
    (htangent : A.tangentKernel H.carrier = ⊤) :
    ∀ᶠ z in 𝓝 (0 : A.ParameterSpace),
      ∀ hz : z ∈ A.domain, A.map ⟨z, hz⟩ ∈ H.carrier := by sorry
