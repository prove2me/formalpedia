-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P52_joint_trace_concavity
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P52.joint_trace_concavity
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:58:30.13612+00:00
-- url     : https://prove2.me/theorems/e5d9b525-faed-47bd-b3a7-e517284a769e
-- title:
--   Appendix A: joint trace concavity extended to positive semidefinite pairs
-- statement:
--   All Hilbert spaces below are finite dimensional and nonzero over $\mathbb C$. A density operator is positive semidefinite with trace one. Every spectral power is zero on the kernel, including zero and negative powers. Information quantities use base-two logarithms, with $\log_2 0=-\infty$; the operator logarithms in exponential formulas are natural logarithms.
--
--   Let $1<a<2$, let $X$ be a nonempty finite set, and let $p_x\ge0$ satisfy $\sum_xp_x=1$. Let $P_x,Q_x$ be positive semidefinite operators on the same space $H$, and set $\overline P=\sum_xp_xP_x$ and $\overline Q=\sum_xp_xQ_x$. Then
--   $$
--   \sum_xp_x\operatorname{Tr}\left[(Q_x^{(a-1)/2}P_xQ_x^{(a-1)/2})^{1/a}\right]
--   \le\operatorname{Tr}\left[(\overline Q^{(a-1)/2}\overline P\overline Q^{(a-1)/2})^{1/a}\right].
--   $$
--   Zero weights and zero or singular operators are allowed.
--
--   This extends the joint trace concavity from positive definite to positive semidefinite pairs.
-- source:
--   Quantum Markov chains, sufficiency of quantum channels, and Renyi information measures, arXiv:1501.05636v4, PDF p. 20, Appendix A: joint trace concavity extended to positive semidefinite pairs

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P52

noncomputable section

open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakethird100.P52

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Dependency50.P21 (channelAdjoint petz marginalAB)

open QAlgorithms.Papers.Independent.Dependency50.P35 (tr elog maxRelative)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Renew46.P35 (HasMarkovBlocks)

/-- Appendix A, PDF p.20, equation (A.12): joint concavity extended
to all positive semidefinite pairs, including zero matrices and zero weights. -/
theorem joint_trace_concavity {H X : Type} [Fintype H] [DecidableEq H] [Nonempty H]
    [Fintype X] [Nonempty X] (a : ℝ) (ha : 1 < a ∧ a < 2)
    (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1)
    (P Q : X → Mat H) (hP : ∀ x, (P x).PosSemidef) (hQ : ∀ x, (Q x).PosSemidef) :
    (∑ x, p x * jointTrace a (P x) (Q x)) ≤
      jointTrace a (∑ x, (p x : ℂ) • P x) (∑ x, (p x : ℂ) • Q x) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P52

end
