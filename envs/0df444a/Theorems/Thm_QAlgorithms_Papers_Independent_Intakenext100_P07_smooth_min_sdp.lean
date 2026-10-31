-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_smooth_min_sdp
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.smooth_min_sdp
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:53:15.575991+00:00
-- url     : https://prove2.me/theorems/3aefa982-34af-4df2-a250-b3ce4f640fce
-- title:
--   §6.2.2 (6.37): smooth min-entropy SDP
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Here $F$ is squared algebraic fidelity, $F_*$ is squared generalized fidelity, $P=\sqrt{1-F_*}$ is purified distance, and $\Delta(\rho,\tau)=\max_{0\le M\le I}|\operatorname{Tr}((\rho-\tau)M)|$. The symbols $H_{\min}$ and $H_{\max}$ denote conditional min- and max-entropy, with values $+\infty$ and $-\infty$ at zero. Smoothing optimizes over all subnormalized states in the purified-distance ball; every entropy radius satisfies $0\le\varepsilon<\sqrt{\operatorname{Tr}\rho}$.
--
--   For normalized center ρ_AB and an actual purification ρ_ABC, exp(−Hmin^ε) is the minimum Trσ_B over σ_B≥0, positive tildeρ_ABC of trace≤1, I_A⊗σ_B≥Tr_C tildeρ, and Tr(tildeρ_ABC ρ_ABC)≥1−ε².
--
--   $$
--   2^{-H_{\min}^\varepsilon(A|B)}=\min\{\operatorname{Tr}\sigma_B:\sigma_B\ge0,\ \widetilde\rho\ge0,\ \operatorname{Tr}\widetilde\rho\le1,\ I_A\otimes\sigma_B\ge\operatorname{Tr}_C\widetilde\rho,\ \operatorname{Tr}(\widetilde\rho\rho_{ABC})\ge1-\varepsilon^2\}.
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 98, §6.2.2 (6.37): smooth min-entropy SDP

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

/-- NODE paper:1504.00233#6.smoothsdp
Equation (6.37), PDF pp.98-99. Printed: F_* squared again in the prose.
Changed: F_* >= 1-e^2. Why: F_* already denotes squared fidelity and the SDP uses overlap 1-e^2. -/
theorem smooth_min_sdp [Nonempty A] [Nonempty B] [Nonempty C] (r : paperMat ((A × B) × C))
    (hr : IsDensityMatrix r) (hp : paperPure r) (e : ℝ) (he : Radius r e) :
    ∃ t : paperMat ((A × B) × C), ∃ s : paperMat B, SmoothPrimal r e t s ∧
      ENNReal.ofReal s.trace.re = expE (-paperSmoothMin (traceRight r) e) ∧
      ∀ t' s', SmoothPrimal r e t' s' → s.trace.re ≤ s'.trace.re := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
