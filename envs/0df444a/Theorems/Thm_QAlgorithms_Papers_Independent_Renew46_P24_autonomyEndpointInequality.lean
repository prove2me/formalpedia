-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P24_autonomyEndpointInequality
-- name    : QAlgorithms.Papers.Independent.Renew46.P24.autonomyEndpointInequality
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:49:15.712816+00:00
-- url     : https://prove2.me/theorems/9493a7ab-ef2a-4435-8fd5-12b7a5eec321
-- title:
--   §4.1 remark: autonomy without a macroscopic semigroup
-- statement:
--   In the microcanonical setting, let $\Omega=\{x:H^{\rm mc}(x)\ge0\}$ and let microscopic unital star automorphisms $\tau_{t,s}^N$ obey their cocycle law for real times $t\ge s\ge0$. Suppose maps $\varphi_{t,s}:\Omega\to\Omega$ satisfy the autonomy condition: for each $x\in\Omega$, one entropy-maximizing concentrating projection sequence $P^N(x)$ reproduces $G(\varphi_{t,s}x)$ in the limit for every ordered analytic test $G$ and every interval. Without assuming the macroscopic semigroup law, one still has
--
--   $$H^{\rm mc}(\varphi_{t,s}x)\ge H^{\rm mc}(x)\qquad(x\in\Omega,\ 0\le s\le t).$$
--
--   This compares an interval endpoint to the configuration supplied as its initial input. It does not compare arbitrary intermediate points along a single trajectory without the semigroup property.
-- source:
--   Quantum Macrostates, Equivalence of Ensembles and an H-Theorem, arXiv:math-ph/0601027v2, PDF p. 13, §4.1 remark: autonomy without a macroscopic semigroup

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P24

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P24

open Filter

open scoped Topology ComplexOrder Matrix.Norms.L2Operator

-- Exact primitives verified against the pinned accepted-library SHA256 catalogue.

open QAlgorithms.Papers.Independent.Information100.P23 (Operator)

open QAlgorithms.Papers.Independent.Dependency50.P21 (spectralFunction relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P10 (pauli)

open QAlgorithms.Papers.Independent.Information100.P71 (SupportIncluded)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.13, section 4.1 remark: without a macroscopic semigroup, autonomy
still compares each interval endpoint with its initial configuration. -/
theorem autonomyEndpointInequality {K : Type*} (S : MacroscopicSystem K)
    (hS : IsMacroscopic S) (tau : AutomorphismDynamics S)
    (htau : AutomorphismCocycle tau) (phi : MacroscopicDynamics K)
    (hautonomy : microcanonicalAutonomy S tau phi) :
    ∀ x, microcanonicalAdmissible S x → ∀ (t s : ℝ), 0 ≤ s → s ≤ t →
      microcanonicalEntropy S x ≤ microcanonicalEntropy S (phi t s x) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P24

end
