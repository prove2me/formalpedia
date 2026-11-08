-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_baire_of_locally_compact_or_complete
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P20.baire_of_locally_compact_or_complete
-- status  : Proved
-- author  : @Gohan
-- created : 2026-11-01T07:56:22.76221+00:00
-- url     : https://prove2.me/theorems/661ba211-bba6-4d18-be1f-dd029e6f2e3e
-- title:
--   borel-baire-quotient-background
-- statement:
--   Every locally compact Hausdorff space is a Baire space, and every complete metric space is a Baire space. Empty spaces are allowed. The Hausdorff convention comes from the source paragraph immediately preceding the claim.
-- source:
--   Observables I: Stone Spectra, arXiv:math-ph/0509020v1, PDF p. 52, borel-baire-quotient-background

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P20

open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- borel-baire-quotient-background; de Groote, Observables I, PDF pp. 52.
Restored in moderation: source background status is not a formalization obstacle. -/
theorem baire_of_locally_compact_or_complete :
    (∀ (M : Type u) [TopologicalSpace M] [T2Space M] [LocallyCompactSpace M], BaireSpace M) ∧
    (∀ (M : Type u) [MetricSpace M] [CompleteSpace M], BaireSpace M) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P20

end
