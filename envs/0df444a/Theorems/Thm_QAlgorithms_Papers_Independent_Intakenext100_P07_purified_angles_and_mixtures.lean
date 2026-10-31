-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_purified_angles_and_mixtures
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.purified_angles_and_mixtures
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:42:48.094687+00:00
-- url     : https://prove2.me/theorems/cffb359b-b371-4d33-8c18-3d908c22ea84
-- title:
--   §3.4 (3.53)–(3.54): angular triangle and quasi-convexity
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Here $F$ is squared algebraic fidelity, $F_*$ is squared generalized fidelity, $P=\sqrt{1-F_*}$ is purified distance, and $\Delta(\rho,\tau)=\max_{0\le M\le I}|\operatorname{Tr}((\rho-\tau)M)|$.
--
--   For positive angles with sum≤π/2, P(ρ,σ)≤sinφ and P(σ,τ)≤sinθ imply P(ρ,τ)≤sin(φ+θ)<sinφ+sinθ. Also P(λρ1+(1−λ)ρ2,λτ1+(1−λ)τ2)≤max_i P(ρi,τi) for 0≤λ≤1.
--
--   $$
--   P(\rho,\tau)\le\sin(\varphi+\vartheta)<\sin\varphi+\sin\vartheta,\qquad P(\lambda\rho_1+(1-\lambda)\rho_2,\lambda\tau_1+(1-\lambda)\tau_2)\le\max_iP(\rho_i,\tau_i).
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 48, §3.4 (3.53)–(3.54): angular triangle and quasi-convexity

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P07

noncomputable section

open Filter

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Intakenext100.P07

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J A B C D X Y Z : Type*}

variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

variable [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

variable [Fintype Z] [DecidableEq Z]

/-- NODE paper:1504.00233#3.purifiedquasiconvex
§3.4 (3.53)–(3.54): angular triangle and quasi-convexity, arXiv:1504.00233v5, PDF p.48. -/
theorem purified_angles_and_mixtures [Nonempty I] :
    (∀ r s t : paperMat I, paperSubnormalized r → paperSubnormalized s → paperSubnormalized t →
      ∀ a b : ℝ, 0 < a → 0 < b → a+b ≤ Real.pi/2 → purified r s ≤ Real.sin a → purified s t ≤ Real.sin b →
      purified r t ≤ Real.sin (a+b) ∧ Real.sin (a+b) < Real.sin a+Real.sin b) ∧
    (∀ r s t u : paperMat I, paperSubnormalized r → paperSubnormalized s → paperSubnormalized t → paperSubnormalized u →
      ∀ a : ℝ, a ∈ Set.Icc 0 1 → purified (paperMix a r s) (paperMix a t u) ≤ max (purified r t) (purified s u)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
