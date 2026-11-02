-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_borel_points_are_isolated_quasipoints
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P20.borel_points_are_isolated_quasipoints
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:42:57.075806+00:00
-- url     : https://prove2.me/theorems/6135d335-e8c0-4c56-806f-bf96f274622e
-- title:
--   Proposition 3.9
-- statement:
--   Let $M$ be Hausdorff, first countable and Lindelöf. A subset $p$ of the Borel sigma algebra is a point, in the countably prime sense, exactly when it is an atomic quasipoint:
--
--   $$p\text{ is a sigma-algebra point}\quad\Longleftrightarrow\quad p\text{ is an isolated quasipoint of }B(M).$$
--
--   First countability and Lindelöf are retained from the section preamble.
-- source:
--   Observables I: Stone Spectra, arXiv:math-ph/0509020v1, PDF p. 50, Proposition 3.9

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P20

open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- Proposition 3.9; de Groote, Observables I, PDF p./pp. 50.
-/
theorem borel_points_are_isolated_quasipoints {M : Type u} [TopologicalSpace M] [T2Space M]
    [FirstCountableTopology M] [LindelofSpace M] (p : Set (BorelSets M)) :
    IsSigmaPoint p ↔ ∃ B : StoneSpectrum (BorelSets M),
      B.val = p ∧ IsOpen ({B} : Set (StoneSpectrum (BorelSets M))) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P20

end
