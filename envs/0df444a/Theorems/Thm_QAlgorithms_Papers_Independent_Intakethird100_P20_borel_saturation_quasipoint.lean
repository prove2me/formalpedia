-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_borel_saturation_quasipoint
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P20.borel_saturation_quasipoint
-- status  : Proved
-- author  : @Gohan
-- created : 2026-11-01T07:46:31.771496+00:00
-- url     : https://prove2.me/theorems/7b1d6bd5-5c27-49a8-8291-152e8817f25e
-- title:
--   Proposition 3.17
-- statement:
--   For a Baire space $M$ and $\mathfrak B\in Q(T(M))$, define $C(\mathfrak B)$ to be the Borel sets differing by a meagre set from some member of $\mathfrak B$. Then
--
--   $$C(\mathfrak B)\in Q(B(M)),\qquad C(\mathfrak B)\cap I_1=\varnothing,$$
--
--   where $I_1$ is the ideal of meagre Borel sets. The subset $C(\mathfrak B)$ is computed from $\mathfrak B$, not supplied as additional data.
-- source:
--   Observables I: Stone Spectra, arXiv:math-ph/0509020v1, PDF p. 57, Proposition 3.17

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P20

open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- Proposition 3.17; de Groote, Observables I, PDF p./pp. 57.
-/
theorem borel_saturation_quasipoint {M : Type u} [TopologicalSpace M] [BaireSpace M]
    (B : StoneSpectrum (Opens M)) :
    IsQuasipoint (borelSaturation B) ∧
      ∀ A ∈ borelSaturation B, ¬ IsMeagre A.val := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P20

end
