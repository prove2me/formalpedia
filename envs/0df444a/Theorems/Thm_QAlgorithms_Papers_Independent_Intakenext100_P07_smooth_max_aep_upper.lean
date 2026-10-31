-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_smooth_max_aep_upper
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.smooth_max_aep_upper
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:30:45.036604+00:00
-- url     : https://prove2.me/theorems/11e69fb9-7a25-46ee-9ee3-847fb2f018d7
-- title:
--   6.23
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Here $F$ is squared algebraic fidelity, $F_*$ is squared generalized fidelity, $P=\sqrt{1-F_*}$ is purified distance, and $\Delta(\rho,\tau)=\max_{0\le M\le I}|\operatorname{Tr}((\rho-\tau)M)|$. The symbols $H_{\min}$ and $H_{\max}$ denote conditional min- and max-entropy, with values $+\infty$ and $-\infty$ at zero. Smoothing optimizes over all subnormalized states in the purified-distance ball; every entropy radius satisfies $0\le\varepsilon<\sqrt{\operatorname{Tr}\rho}$.
--
--   For normalized ρ, positive σ on the SAME system and 0<ε<1, the limit of (1/n)Dmax^ε(ρ^⊗n||σ^⊗n) exists in EReal and is at most D(ρ||σ).
--
--   $$
--   \exists L\in\overline{\mathbb R}:\quad\frac1nD_{\max}^{\varepsilon}(\rho^{\otimes n}\|\sigma^{\otimes n})\longrightarrow L\le D(\rho\|\sigma).
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 109, 6.23

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

/-- NODE paper:1504.00233#6.23
Theorem 6.23, PDF p.109. Printed: sigma in S(B). Changed: sigma on A.
Why: both displayed divergences and equations (6.97)-(6.100) require the same system. -/
theorem smooth_max_aep_upper [Nonempty I] (r s : paperMat I) (hr : IsDensityMatrix r) (hs : s.PosSemidef)
    (e : ℝ) (he : 0 < e) (he1 : e < 1) :
    ∃ L : EReal, Tendsto (fun n : ℕ => ((1/(n:ℝ):ℝ):EReal)*
      smoothMaxD (paperTensorPower r n) (paperTensorPower s n) e) atTop (nhds L) ∧ L ≤ paperRelativeD r s := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
