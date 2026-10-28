-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P40_tenderMeasurementAverage
-- name    : QAlgorithms.Papers.Independent.Claimed50.P40.tenderMeasurementAverage
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T10:50:43.666785+00:00
-- url     : https://prove2.me/theorems/2cd20ae9-8461-425f-a6ad-dc071fa6e71f
-- title:
--   Tender measurement under average recognition error
-- statement:
--   Let $(\rho_a)_{a\in A}$ be normalized states of a finite-dimensional C*-algebra, let $D=(D_b)_{b\in B}$ be a finite POVM, and let $\phi:A\to B$. Let $P$ be a discrete probability distribution on the arbitrary label set $A$, allowing zero weights. Suppose $\bar\epsilon\ge0$ and only the average error is bounded:
--   $$
--   \sum_a P(a)\bigl(1-\operatorname{Tr}(\rho_aD_{\phi(a)})\bigr)\le\bar\epsilon.
--   $$
--   Define $\delta(\rho)=\sum_b\sqrt{D_b}\rho\sqrt{D_b}$ and $\Delta(\rho)=\sum_b|b\rangle\langle b|\otimes\sqrt{D_b}\rho\sqrt{D_b}$. Then
--   $$
--   \begin{aligned}
--   \sum_aP(a)\|\rho_a-\delta(\rho_a)\|_1&\le\sqrt{8\bar\epsilon}+\bar\epsilon,\\
--   \sum_aP(a)\big\||\phi(a)\rangle\langle\phi(a)|\otimes\rho_a-\Delta(\rho_a)\big\|_1
--   &\le\sqrt{8\bar\epsilon}+\bar\epsilon.
--   \end{aligned}
--   $$
--   The trace is intrinsic and the trace norm is unhalved. These are averages of norms; no pointwise error bound is imposed. All sums converge, since the state-difference norms are bounded by two. This is the ensemble version of the disturbance bound, including its continuous zero-error endpoint.
-- source:
--   The Capacity of the Quantum Multiple Access Channel, arXiv:quant-ph/9807019v3, PDF p. 4, Lemma 8 (Average version)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P40

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Claimed50.P40

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma 8 (average version), PDF p.4: a PMF permits arbitrary discrete ensemble labels
and zero weights. Average norms, not the norm of an average; no pointwise error assumption.
The continuous zero-error endpoint is included. -/
theorem tenderMeasurementAverage {A B : Type*} [Fintype B] [DecidableEq B] {d : ℕ}
    (block : Fin d → ℕ) (rho : A → Matrix (Fin d) (Fin d) ℂ)
    (hrho : ∀ a, IsDensityMatrix (rho a) ∧ InBlocks block (rho a))
    (D : B → Matrix (Fin d) (Fin d) ℂ) (hD : IsPOVM D)
    (hblock : ∀ b, InBlocks block (D b)) (phi : A → B) (P : PMF A)
    (epsilonBar : ℝ) (hepsilonBar : 0 ≤ epsilonBar)
    (herror : (∑' a, (P a).toReal * (1 - effectProb (D (phi a)) (rho a))) ≤ epsilonBar) :
    (∑' a, (P a).toReal * traceNorm (rho a - tenderOperation D (rho a))) ≤
      Real.sqrt (8 * epsilonBar) + epsilonBar ∧
    (∑' a, (P a).toReal *
      traceNorm (idealLabel (phi a) (rho a) - labelledOperation D (rho a))) ≤
      Real.sqrt (8 * epsilonBar) + epsilonBar := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P40

end
