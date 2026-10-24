-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P20_testingDivergence_dataProcessing
-- name    : QAlgorithms.Papers.Independent.Support50.P20.testingDivergence_dataProcessing
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:32:42.624887+00:00
-- url     : https://prove2.me/theorems/2b2d52b2-2bf8-4530-8d64-cf551f315a77
-- title:
--   Data processing of testing divergence
-- statement:
--   Let $\rho,\sigma$ be normalized positive trace-class operators on a complex Hilbert space $H$, let $K$ be another complex Hilbert space, and let $\mathcal E$ be a complex-linear, completely positive, trace-preserving map from trace-class operators on $H$ to trace-class operators on $K$. Complete positivity means positivity at every finite matrix amplification. For $0\le\epsilon<1$, the hypothesis-testing divergence in bits satisfies
--
--   $$
--   D_H^\epsilon\bigl(\mathcal E(\rho)\|\mathcal E(\sigma)\bigr)\le D_H^\epsilon(\rho\|\sigma).
--   $$
--
--   Physical preprocessing therefore cannot improve distinguishability as measured by this divergence. The result includes infinite-dimensional spaces and infinite divergence, with no finite Kraus-rank restriction.
--
--   **Formalization Note** The source's CPM is read as physical trace-preserving preprocessing, as required by its proof that pulls a complete measurement back to a complete measurement.
-- source:
--   One-Shot Classical-Quantum Capacity and Hypothesis Testing, arXiv:1007.5456v3, PDF p. 2, Property 2: data processing of hypothesis-testing divergence

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P20

noncomputable section

open Filter

open scoped ENNReal

namespace QAlgorithms.Papers.Independent.Support50.P20

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P13
  (IsTraceClass IsPositive operatorTrace State)

open QAlgorithms.Papers.Independent.Information100.P63 (logTwo)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- PDF p.2, Property 2 and its proof: DPI for physical (CPTP) preprocessing
between arbitrary output Hilbert spaces, with all finite CP amplifications. -/
theorem testingDivergence_dataProcessing {I J K : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (b : HilbertBasis I ℂ H) (d : HilbertBasis J ℂ K)
    (rho sigma : State b) (Phi : (H →L[ℂ] H) → (K →L[ℂ] K))
    (hPhi : IsHilbertCPTP b d Phi) (epsilon : ℝ)
    (hZero : 0 ≤ epsilon) (hOne : epsilon < 1) :
    hilbertTestingDivergence d epsilon (Phi rho.val.val) (Phi sigma.val.val) ≤
      hilbertTestingDivergence b epsilon rho.val.val sigma.val.val := by sorry

end QAlgorithms.Papers.Independent.Support50.P20

end
