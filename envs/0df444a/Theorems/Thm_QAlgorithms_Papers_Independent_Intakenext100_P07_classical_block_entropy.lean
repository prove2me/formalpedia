-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_classical_block_entropy
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.classical_block_entropy
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:50:32.612003+00:00
-- url     : https://prove2.me/theorems/65a49dfb-1a4f-4998-9307-78bf6d1abe01
-- title:
--   §6.1.4 (6.25)–(6.27): conditioning on a classical register
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Here $F$ is squared algebraic fidelity, $F_*$ is squared generalized fidelity, $P=\sqrt{1-F_*}$ is purified distance, and $\Delta(\rho,\tau)=\max_{0\le M\le I}|\operatorname{Tr}((\rho-\tau)M)|$. The symbols $H_{\min}$ and $H_{\max}$ denote conditional min- and max-entropy, with values $+\infty$ and $-\infty$ at zero. Smoothing optimizes over all subnormalized states in the purified-distance ball; every entropy radius satisfies $0\le\varepsilon<\sqrt{\operatorname{Tr}\rho}$.
--
--   Let p_y>=0 with sum_y p_y<=1 and let each conditional rhohat_AB(y) be normalized. Assemble the actual classical block state sum_y p_y rhohat_AB(y) tensor |y><y|. The displayed min- and max-entropy identities hold, including zero total mass. For any normalized classical joint law, the optimal guessing probability is sum_y max_x p(x,y)=2^(-Hmin(X|Y)).
--
--   $$
--   H_{\min}(A|BY)=-\log_2\sum_y p_y2^{-H_{\min}(A|B)_{\widehat\rho_y}},\qquad H_{\max}(A|BY)=\log_2\sum_y p_y2^{H_{\max}(A|B)_{\widehat\rho_y}}.
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 96, §6.1.4 (6.25)–(6.27): conditioning on a classical register

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

/-- NODE paper:1504.00233#6.classicalconditioning
§6.1.4 (6.25)–(6.27): conditioning on a classical register, arXiv:1504.00233v5, PDF p.96. -/
theorem classical_block_entropy [Nonempty A] [Nonempty B] [Nonempty X] [Nonempty Y]
    (p : Y → ℝ) (hp : ∀ y, 0 ≤ p y) (ht : ∑ y, p y ≤ 1)
    (r : Y → paperMat (A × B)) (hr : ∀ y, IsDensityMatrix (r y)) :
    paperHmin (conditionalBlocks (fun y => (p y:ℂ) • r y)) = 
      -paperLogE (∑ y, p y*(2:ℝ)^(-(paperHmin (r y)).toReal)) ∧
    hmax (conditionalBlocks (fun y => (p y:ℂ) • r y)) = 
      paperLogE (∑ y, p y*(2:ℝ)^(hmax (r y)).toReal) ∧
    (∀ q : X × Y → ℝ, paperProbability q →
      expE (-paperHmin (Matrix.diagonal (fun xy => (q xy:ℂ)))) = 
        ENNReal.ofReal (∑ y, sSup {v : ℝ | ∃ x, v = q (x,y)})) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
