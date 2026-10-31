-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_max_alberti
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.max_alberti
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:21:09.239996+00:00
-- url     : https://prove2.me/theorems/14c33a00-e8b8-461d-b6d4-27acbcbc0d8b
-- title:
--   6.6
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Here $F$ is squared algebraic fidelity, $F_*$ is squared generalized fidelity, $P=\sqrt{1-F_*}$ is purified distance, and $\Delta(\rho,\tau)=\max_{0\le M\le I}|\operatorname{Tr}((\rho-\tau)M)|$. The symbols $H_{\min}$ and $H_{\max}$ denote conditional min- and max-entropy, with values $+\infty$ and $-\infty$ at zero. Smoothing optimizes over all subnormalized states in the purified-distance ball; every entropy radius satisfies $0\le\varepsilon<\sqrt{\operatorname{Tr}\rho}$.
--
--   exp(Hmax(A|B)_ρ)=inf_{Y_AB>0} Tr(ρ_AB Y_AB^{-1}) ||Tr_A Y_AB||∞. The inverse is the actual inverse on this positive definite domain; an infimum, not necessarily attained.
--
--   $$
--   2^{H_{\max}(A|B)_\rho}=\inf_{Y_{AB}>0}\operatorname{Tr}(\rho_{AB}Y_{AB}^{-1})\|\operatorname{Tr}_A Y_{AB}\|_\infty.
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 95, 6.6

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

/-- NODE paper:1504.00233#6.6
6.6, arXiv:1504.00233v5, PDF p.95. -/
theorem max_alberti [Nonempty A] [Nonempty B] (r : paperMat (A × B)) (hr : paperSubnormalized r) :
    expE (hmax r) = sInf {v : ENNReal | ∃ Y : paperMat (A × B), Y.PosDef ∧
      v = ENNReal.ofReal ((r*Y⁻¹).trace.re*‖traceLeft Y‖)} := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
