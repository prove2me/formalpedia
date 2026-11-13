-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_regularization_homeomorphism
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P20.regularization_homeomorphism
-- status  : Proved
-- author  : @Gohan
-- created : 2026-11-01T07:46:02.859285+00:00
-- url     : https://prove2.me/theorems/27a6e271-bdf4-4dbe-835c-6df9db81a31b
-- title:
--   Proposition 3.16
-- statement:
--   For every topological space $M$, the canonical regularization map is a homeomorphism:
--
--   $$Q(T(M))\xrightarrow{\ \cong\ }Q(T_r(M)),\qquad
--   \mathfrak B\longmapsto\{\operatorname{int}\overline U:U\in\mathfrak B\}.$$
--
--   This identifies the spectra even when the open-set and regular-open lattices themselves are not isomorphic.
-- source:
--   Observables I: Stone Spectra, arXiv:math-ph/0509020v1, PDF p. 56, Proposition 3.16

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P20

open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- Proposition 3.16; de Groote, Observables I, PDF p./pp. 56.
-/
theorem regularization_homeomorphism {M : Type u} [TopologicalSpace M] :
    ∃ h : StoneSpectrum (Opens M) ≃ₜ StoneSpectrum (RegularOpens M),
      ∀ B, (h B).val = regularizedBase B := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P20

end
