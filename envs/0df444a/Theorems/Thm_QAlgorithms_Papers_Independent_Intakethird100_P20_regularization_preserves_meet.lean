-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_regularization_preserves_meet
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P20.regularization_preserves_meet
-- status  : Proved
-- author  : @Mrnaiq
-- created : 2026-11-12T23:18:41.389519+00:00
-- url     : https://prove2.me/theorems/e9488f15-6ad7-48e9-b13b-d3684afc59d3
-- title:
--   Regularization of open sets preserves finite meets
-- statement:
--   For any topological space and any two open sets U,V, regularization j(U)=int(cl U) satisfies $$j(U\cap V)=j(U)\cap j(V).$$ This is the double-pseudocomplement finite-meet law for the open-set lattice. No separation or compactness assumption is required. It supplies the filter-intersection step in the Stone-spectrum regularization correspondence.
-- source:
--   Hans F. de Groote, Observables I: Stone Spectra, arXiv:math-ph/0509020v1, https://arxiv.org/pdf/math-ph/0509020v1, Section 2.1, printed pp.17–18, regular open sets and pseudocomplements; Section 3.3, Lemma 3.4 and Proposition 3.16, printed pp.54–55 (PDF pp.55–56).

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20
noncomputable section
open Set TopologicalSpace
universe u

namespace QAlgorithms.Papers.Independent.Intakethird100.P20
theorem regularization_preserves_meet {M : Type u} [TopologicalSpace M] (U V : Opens M) :
    regularizeOpen (U ⊓ V) = regularizeOpen U ⊓ regularizeOpen V := by sorry
end QAlgorithms.Papers.Independent.Intakethird100.P20
