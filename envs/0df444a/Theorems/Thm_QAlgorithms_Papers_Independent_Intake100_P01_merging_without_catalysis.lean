-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P01_merging_without_catalysis
-- name    : QAlgorithms.Papers.Independent.Intake100.P01.merging_without_catalysis
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:53:09.979274+00:00
-- url     : https://prove2.me/theorems/25257e0a-93e8-4526-8ba9-1344076ce38a
-- title:
--   Remark 7: optimal merging without entanglement catalysis
-- statement:
--   For every finite pure source $|\psi\rangle_{ABR}$, put $s=S(AB)-S(B)$. There exists a sequence of physical one-way Alice-to-Bob LOCC merging codes on every positive blocklength, with positive integer input and output Bell ranks $K_n,L_n$, full-output fidelity tending to one, and
--   $$\frac{\log_2K_n-\log_2L_n}{n}\longrightarrow s.$$
--   If $s<0$, the sequence has $K_n=1$ for every blocklength. If $s\ge0$, it has $L_n=1$ for every blocklength. This strengthens optimal net cost by excluding entanglement catalysis; at $s=0$ the consumed entanglement may be sublinear.
-- source:
--   Quantum state merging and negative information, arXiv:quant-ph/0512247v1, PDF p. 9, Remark 7: optimal merging without entanglement catalysis

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P01

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P01

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

open MeasureTheory

open QAlgorithms.Papers.Independent.Gap20.P11 (IsLOCC productApply finTransport referenceInformation)

open QAlgorithms.Papers.Independent.Bridge50.P40
  (RankMergingCode OneWayMergingCode mergingFidelity SourceProtocolAchievable)

open QAlgorithms.Papers.Independent.Dependency50.P19
  (first marginalRA marginalRB motherTarget motherOutput sourceCopies swap mutualInformation)

open QAlgorithms.Papers.Independent.Information100.P67 (conditionalEntropy)

open QAlgorithms.Papers.Independent.Information100.P32 (purity)

open QAlgorithms.Papers.Independent.Advance50.P29 (weakTypicalProjector)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.9, Remark 7: optimal rates with K=1 in the negative regime,
L=1 in the nonnegative regime. At zero entropy the input can be sublinear;
zero finite-block entanglement is not asserted. -/
theorem merging_without_catalysis {A B R : Type}
    [Fintype A] [Fintype B] [Fintype R] [Nonempty A] [Nonempty B] [Nonempty R]
    (psi : EuclideanSpace ℂ (R × (A × B))) (hpsi : IsState psi) :
    let s := conditionalEntropy (traceLeft (pureDensity psi))
    ∃ P : (n : ℕ) → OneWayMergingCode A B (n+1),
      (∀ n, IsLOCC (P n).operation) ∧
      (∀ n, (s < 0 → (P n).K = 1) ∧ (0 ≤ s → (P n).L = 1)) ∧
      Filter.Tendsto (fun n =>
        (Real.logb 2 ((P n).K : ℝ) - Real.logb 2 ((P n).L : ℝ)) / (n+1 : ℕ))
        Filter.atTop (nhds s) ∧
      Filter.Tendsto (fun n => mergingFidelity psi (n+1)
        (P n).K (P n).L (P n).operation) Filter.atTop (nhds 1) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P01

end
