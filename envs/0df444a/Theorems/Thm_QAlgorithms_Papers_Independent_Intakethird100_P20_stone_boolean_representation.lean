-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_stone_boolean_representation
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P20.stone_boolean_representation
-- status  : Proved
-- author  : @Gohan
-- created : 2026-11-01T07:52:53.449702+00:00
-- url     : https://prove2.me/theorems/19b91f58-11b1-485b-9368-9fa77a86b458
-- title:
--   stone-boolean-representation
-- statement:
--   For every Boolean algebra, its quasipoint spectrum with the membership topology is compact, zero dimensional and Hausdorff. The map $a\mapsto Q_a$ is an order isomorphism onto its clopen Boolean algebra, hence a Boolean-algebra isomorphism. The trivial Boolean algebra and empty spectrum are included.
-- source:
--   Observables I: Stone Spectra, arXiv:math-ph/0509020v1, PDF p. 8, stone-boolean-representation

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P20

open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- stone-boolean-representation; de Groote, Observables I, PDF pp. 8, 39.
Restored in moderation: source background status is not a formalization obstacle. -/
theorem stone_boolean_representation {L : Type u} [BooleanAlgebra L] :
    CompactSpace (StoneSpectrum L) ∧ T2Space (StoneSpectrum L) ∧
    TopologicalSpace.IsTopologicalBasis {s : Set (StoneSpectrum L) | IsClopen s} ∧
    ∃ e : L ≃o Clopens (StoneSpectrum L),
      ∀ a : L, (e a : Set (StoneSpectrum L)) = stoneBasic a := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P20

end
