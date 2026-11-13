-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_quasipoint_regularization_membership
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P20.quasipoint_regularization_membership
-- status  : Proved
-- author  : @Mrnaiq
-- created : 2026-11-12T23:18:44.583272+00:00
-- url     : https://prove2.me/theorems/12643447-468e-4d09-8877-5bb333801fac
-- title:
--   Open-set quasipoints preserve membership under regularization
-- statement:
--   For every quasipoint B of the lattice of open sets of an arbitrary topological space, and every open U, $$U\in B\quad\Longleftrightarrow\quad\operatorname{int}(\overline U)\in B.$$ Here a quasipoint is a maximal proper nonempty filter base. The statement concerns membership in the original open-set quasipoint; it is the dense-open membership step behind the regular-open spectrum correspondence.
-- source:
--   Hans F. de Groote, Observables I: Stone Spectra, arXiv:math-ph/0509020v1, https://arxiv.org/pdf/math-ph/0509020v1, Section 3.3, Lemma 3.4 and the membership equivalence in the proof of Proposition 3.16, printed pp.54–55 (PDF pp.55–56).

import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_quasipoint_upward_and_meet_closed
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_quasipoint_nonmember_has_disjoint_member
import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20
noncomputable section
open Set TopologicalSpace
universe u

namespace QAlgorithms.Papers.Independent.Intakethird100.P20
theorem quasipoint_regularization_membership {M : Type u} [TopologicalSpace M]
    (B : StoneSpectrum (Opens M)) (U : Opens M) :
    U ∈ B.val ↔ regularizeOpen U ∈ B.val := by sorry
end QAlgorithms.Papers.Independent.Intakethird100.P20
