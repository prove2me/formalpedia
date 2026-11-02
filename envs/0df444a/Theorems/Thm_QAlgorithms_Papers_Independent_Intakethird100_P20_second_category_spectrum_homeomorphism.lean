-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_second_category_spectrum_homeomorphism
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P20.second_category_spectrum_homeomorphism
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:47:23.059206+00:00
-- url     : https://prove2.me/theorems/76da9591-fb78-4ce8-bece-850765b810c6
-- title:
--   Proposition 3.18
-- statement:
--   For a Baire space $M$, the saturation map is a homeomorphism onto the subspace of second-category Borel quasipoints:
--
--   $$\pi_M:Q(T(M))\xrightarrow{\ \cong\ }Q^2(B(M)),\qquad
--   \mathfrak B\longmapsto C(\mathfrak B).$$
--
--   Here $Q^2(B(M))$ consists of quasipoints containing no meagre Borel set and carries the subspace topology. The target is not the full Borel Stone spectrum.
-- source:
--   Observables I: Stone Spectra, arXiv:math-ph/0509020v1, PDF p. 58, Proposition 3.18

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P20

open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- Proposition 3.18; de Groote, Observables I, PDF p./pp. 58.
-/
theorem second_category_spectrum_homeomorphism {M : Type u} [TopologicalSpace M] [BaireSpace M] :
    ∃ h : StoneSpectrum (Opens M) ≃ₜ
      {C : StoneSpectrum (BorelSets M) // ∀ A ∈ C.val, ¬ IsMeagre A.val},
      ∀ B, (h B).val.val = borelSaturation B := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P20

end
