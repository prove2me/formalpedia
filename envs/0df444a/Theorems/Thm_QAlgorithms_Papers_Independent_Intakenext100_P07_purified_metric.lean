-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_purified_metric
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.purified_metric
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:02:25.522971+00:00
-- url     : https://prove2.me/theorems/1adfdd57-c529-4fe9-bd67-81fbda01db3c
-- title:
--   3.16
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Here $F$ is squared algebraic fidelity, $F_*$ is squared generalized fidelity, $P=\sqrt{1-F_*}$ is purified distance, and $\Delta(\rho,\tau)=\max_{0\le M\le I}|\operatorname{Tr}((\rho-\tau)M)|$.
--
--   P is a metric on all subnormalized states. If P(ρ,σ)^2+P(σ,τ)^2≤1 then P(ρ,τ)≤P(ρ,σ) sqrt(F_*(σ,τ))+P(σ,τ) sqrt(F_*(ρ,σ)).
--
--   $$
--   P(\rho,\tau)\le P(\rho,\sigma)\sqrt{F_*(\sigma,\tau)}+P(\sigma,\tau)\sqrt{F_*(\rho,\sigma)}.
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 48, 3.16

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

/-- NODE paper:1504.00233#3.16
3.16, arXiv:1504.00233v5, PDF p.48. -/
theorem purified_metric [Nonempty I] :
    (∀ r s : paperMat I, paperSubnormalized r → paperSubnormalized s →
      0 ≤ purified r s ∧ (purified r s = 0 ↔ r = s) ∧ purified r s = purified s r) ∧
    (∀ r s t : paperMat I, paperSubnormalized r → paperSubnormalized s → paperSubnormalized t →
      purified r t ≤ purified r s+purified s t) ∧
    (∀ r s t : paperMat I, paperSubnormalized r → paperSubnormalized s → paperSubnormalized t →
      purified r s^2+purified s t^2 ≤ 1 → purified r t ≤ purified r s*Real.sqrt (paperGeneralizedFidelity s t)+
        purified s t*Real.sqrt (paperGeneralizedFidelity r s)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
