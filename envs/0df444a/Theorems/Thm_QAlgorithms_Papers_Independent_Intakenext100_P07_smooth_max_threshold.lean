-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_smooth_max_threshold
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.smooth_max_threshold
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:30:06.262991+00:00
-- url     : https://prove2.me/theorems/82cc5b21-399f-4377-8151-bde333533f21
-- title:
--   6.21
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Here $F$ is squared algebraic fidelity, $F_*$ is squared generalized fidelity, $P=\sqrt{1-F_*}$ is purified distance, and $\Delta(\rho,\tau)=\max_{0\le M\le I}|\operatorname{Tr}((\rho-\tau)M)|$. The symbols $H_{\min}$ and $H_{\max}$ denote conditional min- and max-entropy, with values $+\infty$ and $-\infty$ at zero. Smoothing optimizes over all subnormalized states in the purified-distance ball; every entropy radius satisfies $0\le\varepsilon<\sqrt{\operatorname{Tr}\rho}$.
--
--   For subnormalized ρ,σ≥0 and finite real λ≤Dmax(ρ||σ), define Σ=(ρ−exp(λ)σ)_+ and ε=sqrt(2TrΣ−(TrΣ)^2). Then Dmax^ε(ρ||σ)≤λ; Σ and ε are computed, not free witnesses.
--
--   $$
--   D_{\max}^{\varepsilon}(\rho\|\sigma)\le\lambda,\quad\Sigma=(\rho-2^\lambda\sigma)_+,\quad\varepsilon=\sqrt{2\operatorname{Tr}\Sigma-(\operatorname{Tr}\Sigma)^2}.
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 106, 6.21

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

/-- NODE paper:1504.00233#6.21
6.21, arXiv:1504.00233v5, PDF p.106,107. -/
theorem smooth_max_threshold [Nonempty I] (r s : paperMat I) (hr : paperSubnormalized r) (hs : s.PosSemidef)
    (l : ℝ) (hl : (l:EReal) ≤ maxD r s) : smoothMaxD r s (excessRadius r s l) ≤ (l:EReal) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
