-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_delta_jointConvex
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.delta_jointConvex
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:58:11.393295+00:00
-- url     : https://prove2.me/theorems/bb653859-8fe1-409f-b7fb-7f15ea2dd61c
-- title:
--   §3.2 (3.26): joint convexity of generalized trace distance
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Here $F$ is squared algebraic fidelity, $F_*$ is squared generalized fidelity, $P=\sqrt{1-F_*}$ is purified distance, and $\Delta(\rho,\tau)=\max_{0\le M\le I}|\operatorname{Tr}((\rho-\tau)M)|$.
--
--   For 0≤λ≤1, Δ(λρ1+(1−λ)ρ2,λτ1+(1−λ)τ2)≤λΔ(ρ1,τ1)+(1−λ)Δ(ρ2,τ2).
--
--   $$
--   \Delta(\lambda\rho_1+(1-\lambda)\rho_2,\lambda\tau_1+(1-\lambda)\tau_2)\le\lambda\Delta(\rho_1,\tau_1)+(1-\lambda)\Delta(\rho_2,\tau_2).
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 43, §3.2 (3.26): joint convexity of generalized trace distance

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

/-- NODE paper:1504.00233#3.traceconvexity
§3.2 (3.26): joint convexity of generalized trace distance, arXiv:1504.00233v5, PDF p.43,44. -/
theorem delta_jointConvex [Nonempty I] (r s t u : paperMat I) (a : ℝ) (ha : a ∈ Set.Icc 0 1) :
    paperDelta (paperMix a r s) (paperMix a t u) ≤ a*paperDelta r t+(1-a)*paperDelta s u := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
