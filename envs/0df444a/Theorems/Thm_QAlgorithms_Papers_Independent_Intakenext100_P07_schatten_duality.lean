-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_schatten_duality
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.schatten_duality
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:57:02.334347+00:00
-- url     : https://prove2.me/theorems/4fb3e703-10db-4abb-a85b-1a39c7f97d8e
-- title:
--   §3.1.1 (3.11): Schatten norm duality
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Here $F$ is squared algebraic fidelity, $F_*$ is squared generalized fidelity, $P=\sqrt{1-F_*}$ is purified distance, and $\Delta(\rho,\tau)=\max_{0\le M\le I}|\operatorname{Tr}((\rho-\tau)M)|$.
--
--   For conjugate p,q>1, ||L||_p is the maximum of |Tr L†K| over ||K||_q≤1, attained.
--
--   $$
--   \|L\|_p=\max_{\|K\|_q\le1}|\operatorname{Tr}(L^\dagger K)|,\qquad p,q>1,\quad1/p+1/q=1.
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 41, §3.1.1 (3.11): Schatten norm duality

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

/-- NODE paper:1504.00233#3.normduality
§3.1.1 (3.11): Schatten norm duality, arXiv:1504.00233v5, PDF p.41. -/
theorem schatten_duality [Nonempty I] (L : paperMat I) (p q : ℝ) (hp : 1 < p) (hq : 1 < q) (hc : 1/p+1/q = 1) :
    (∃ K : paperMat I, paperSchatten K q ≤ 1 ∧ ‖(Lᴴ*K).trace‖ = paperSchatten L p) ∧
    ∀ K : paperMat I, paperSchatten K q ≤ 1 → ‖(Lᴴ*K).trace‖ ≤ paperSchatten L p := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
