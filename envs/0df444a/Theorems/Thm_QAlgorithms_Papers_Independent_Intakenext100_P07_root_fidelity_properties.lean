-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_root_fidelity_properties
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.root_fidelity_properties
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:42:14.732872+00:00
-- url     : https://prove2.me/theorems/12e1fe1b-6bb7-4f94-9370-18a1a7654f95
-- title:
--   §§3.3–3.3.1: root-fidelity curvature and extension
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Here $F$ is squared algebraic fidelity, $F_*$ is squared generalized fidelity, $P=\sqrt{1-F_*}$ is purified distance, and $\Delta(\rho,\tau)=\max_{0\le M\le I}|\operatorname{Tr}((\rho-\tau)M)|$.
--
--   Root algebraic fidelity is jointly concave on positive operators. Squared algebraic fidelity is nondecreasing under CPTP maps and obeys the displayed congruence identity. For subnormalized states, adjoining a vacuum flag of mass 1-Tr rho defines the normalized hat state; generalized fidelity has the displayed hat identity. Its square root is jointly concave, and generalized fidelity is separately concave in each argument.
--
--   $$
--   \sqrt{F}\text{ is jointly concave},\quad F(L\rho L^\dagger,\tau)=F(\rho,L^\dagger\tau L),\quad F_*(\rho,\tau)=F(\widehat\rho,\widehat\tau).
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 44, §§3.3–3.3.1: root-fidelity curvature and extension

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

/-- NODE paper:1504.00233#3.fidelityproperties
§§3.3–3.3.1: root-fidelity curvature and extension, arXiv:1504.00233v5, PDF p.44,45,46. -/
theorem root_fidelity_properties [Nonempty I] [Nonempty J] :
    (∀ r s t u : paperMat I, r.PosSemidef → s.PosSemidef → t.PosSemidef → u.PosSemidef →
      ∀ l : ℝ, l ∈ Set.Icc 0 1 → l*rootFidelity r s+(1-l)*rootFidelity t u ≤ rootFidelity (paperMix l r t) (paperMix l s u)) ∧
    (∀ E : paperMat I →ₗ[ℂ] paperMat J, paperCPTP E → ∀ r s : paperMat I, r.PosSemidef → s.PosSemidef → paperFidelity r s ≤ paperFidelity (E r) (E s)) ∧
    (∀ r s L : paperMat I, r.PosSemidef → s.PosSemidef → paperFidelity (L*r*Lᴴ) s = paperFidelity r (Lᴴ*s*L)) ∧
    (∀ r s : paperMat I, paperSubnormalized r → paperSubnormalized s →
      paperGeneralizedFidelity r s = paperGeneralizedFidelity (hatState r) (hatState s) ∧ paperGeneralizedFidelity r s = paperFidelity (hatState r) (hatState s)) ∧
    (∀ r s t u : paperMat I, paperSubnormalized r → paperSubnormalized s → paperSubnormalized t → paperSubnormalized u →
      ∀ l : ℝ, l ∈ Set.Icc 0 1 →
      l*Real.sqrt (paperGeneralizedFidelity r s)+(1-l)*Real.sqrt (paperGeneralizedFidelity t u) ≤ Real.sqrt (paperGeneralizedFidelity (paperMix l r t) (paperMix l s u))) ∧
    (∀ r s t : paperMat I, paperSubnormalized r → paperSubnormalized s → paperSubnormalized t → ∀ l : ℝ, l ∈ Set.Icc 0 1 →
      l*paperGeneralizedFidelity r t+(1-l)*paperGeneralizedFidelity s t ≤ paperGeneralizedFidelity (paperMix l r s) t ∧
      l*paperGeneralizedFidelity t r+(1-l)*paperGeneralizedFidelity t s ≤ paperGeneralizedFidelity t (paperMix l r s)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
