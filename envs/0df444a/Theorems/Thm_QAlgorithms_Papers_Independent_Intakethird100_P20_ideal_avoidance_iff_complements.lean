-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_ideal_avoidance_iff_complements
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P20.ideal_avoidance_iff_complements
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:43:19.895457+00:00
-- url     : https://prove2.me/theorems/61dd156f-54aa-4ff7-8a48-4cdfac1e6053
-- title:
--   rem-3.2
-- statement:
--   Let $I$ be a sigma ideal in a countably complete Boolean algebra $L$ and let $\mathfrak B$ be a quasipoint. Then
--
--   $$\mathfrak B\cap I=\varnothing\quad\Longleftrightarrow\quad
--   \{a^\perp:a\in I\}\subseteq\mathfrak B.$$
--
--   The quasipoint hypothesis is essential; this equivalence is not claimed for arbitrary subsets.
-- source:
--   Observables I: Stone Spectra, arXiv:math-ph/0509020v1, PDF p. 54, rem-3.2

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P20

open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- rem-3.2; de Groote, Observables I, PDF p./pp. 54.
-/
theorem ideal_avoidance_iff_complements {L : Type u} [BooleanAlgebra L] (hcomplete : IsSigmaComplete L)
    (I : Set L) (hI : IsSigmaIdeal I) (B : StoneSpectrum L) :
    B.val ∩ I = ∅ ↔ (fun a : L => aᶜ) '' I ⊆ B.val := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P20

end
