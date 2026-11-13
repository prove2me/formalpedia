-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_stonean_clopens_recover_space
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P20.stonean_clopens_recover_space
-- status  : Proved
-- author  : @Gohan
-- created : 2026-11-01T07:52:09.734368+00:00
-- url     : https://prove2.me/theorems/f50eaf9e-115a-4286-ad59-6f75bf06114c
-- title:
--   Lemma 3.8
-- statement:
--   For a Stonean space $\Omega$—compact, Hausdorff and extremally disconnected—the Stone spectrum of its clopen-set Boolean algebra is canonically homeomorphic to $\Omega$:
--
--   $$Q(OC(\Omega))\xrightarrow{\ \cong\ }\Omega,\qquad
--   \mathfrak B\longmapsto\text{the unique point of }\bigcap_{U\in\mathfrak B}U.$$
--
--   The arbitrary join of clopens in this regime is the closure of their union, while the meet is the interior of their intersection; quasipoints only require their usual inclusion order.
-- source:
--   Observables I: Stone Spectra, arXiv:math-ph/0509020v1, PDF p. 72, Lemma 3.8

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P20

open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- Lemma 3.8; de Groote, Observables I, PDF p./pp. 72.
-/
theorem stonean_clopens_recover_space {M : Type u} [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [ExtremallyDisconnected M] :
    ∃ h : StoneSpectrum (Clopens M) ≃ₜ M,
      ∀ B, (⋂ U : {U : Clopens M // U ∈ B.val}, (U.val : Set M)) = {h B} := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P20

end
