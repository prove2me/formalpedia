-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_multipleSourceRegionProperties
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.multipleSourceRegionProperties
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:14:15.679321+00:00
-- url     : https://prove2.me/theorems/bbef4017-cbfe-4dda-81c6-9d1d4078732a
-- title:
--   IV-source-region-properties: Applicable source regions are closed, convex, upward closed; Rq,Fe⊆Rq,Fbar⊆Ra,Fbar; Rq,Fbar=Rq,Dbar and Ra,Fbar=Ra,Dbar.
-- statement:
--   For a finite pure-letter iid multiple source, use actual separate CPTP quantum encoders and a joint CPTP decoder, with all component rates converging and the chosen error vanishing. Every defined rate region is closed, convex and upward closed. The Fe region is asserted only for fully quantum systems; the arbitrary-encoder regions and corresponding inclusions are asserted only for product-letter ensembles, whose joint law may still be correlated.
--
--   $$
--   \mathcal R_{q,F_e}\subseteq\mathcal R_{q,\bar F}=\mathcal R_{q,\bar D}\subseteq\mathcal R_{a,\bar F}=\mathcal R_{a,\bar D}.
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 46, IV-source-region-properties

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P43

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P43

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal Matrix.Norms.L2Operator

open Filter MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

open QAlgorithms.Papers.Independent.Information100.P06 (Below)

open QAlgorithms.Papers.Independent.Information100.P60 (copies relativeBits)

open QAlgorithms.Papers.Independent.Dependency50.P19 (count both)

open QAlgorithms.Papers.Independent.Information100.P22 (coherentInformation)

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P40 (InBlocks)

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P43.matrixMeasurableSpace

/-- Unnumbered source-region properties, PDF p.46. The arbitrary part is restricted
to product-letter ensembles and Fe to full matrix systems. All equivalences/inclusions
in the printed diagram are retained. -/
theorem multipleSourceRegionProperties {s : ℕ} {L : Type*} [Fintype L]
    (S : MultipleData s L) (hS : S.Valid) :
    SourceRegionProperties (quantumSourceRegion S) ∧
    SourceRegionProperties (quantumSourceRegion S true) ∧
    quantumSourceRegion S = quantumSourceRegion S true ∧
    (∀ hfull : ∀ i a b, (S.system i).block a = (S.system i).block b,
      SourceRegionProperties (entanglementSourceRegion S hfull) ∧
      entanglementSourceRegion S hfull ⊆ quantumSourceRegion S) ∧
    (∀ P : ProductData s, P.Valid →
      SourceRegionProperties (arbitrarySourceRegion P) ∧
      SourceRegionProperties (arbitrarySourceRegion P true) ∧
      arbitrarySourceRegion P = arbitrarySourceRegion P true ∧
      quantumSourceRegion P.multiple ⊆ arbitrarySourceRegion P) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end
