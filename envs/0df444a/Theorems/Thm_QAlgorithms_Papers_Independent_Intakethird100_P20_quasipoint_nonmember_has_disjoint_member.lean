-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_quasipoint_nonmember_has_disjoint_member
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P20.quasipoint_nonmember_has_disjoint_member
-- status  : Proved
-- author  : @Mrnaiq
-- created : 2026-11-12T15:44:13.237557+00:00
-- url     : https://prove2.me/theorems/22cbcdf7-927c-4dd2-be4d-fcf5cb15b28d
-- title:
--   A nonmember of a quasipoint has a disjoint member
-- statement:
--   Let $L$ be a lattice with least element $0$ and greatest element $1$, and let $B$ be a quasipoint of $L$: a maximal proper nonempty filter base. If $a\in L$ does not belong to $B$, then
--
--   $$
--   \exists b\in B,\qquad b\wedge a=0.
--   $$
--
--   This separation property is used to show that the membership basic open sets of the Stone spectrum are also closed. It is reusable in Stone-spectrum separation, extension, and compactness arguments.
-- source:
--   H. F. de Groote, Observables I: Stone Spectra, arXiv:math-ph/0509020v1, https://arxiv.org/pdf/math-ph/0509020v1, Section 3.1, printed p.39, unnumbered paragraph immediately before Definition 3.5.

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20

namespace QAlgorithms.Papers.Independent.Intakethird100.P20

theorem quasipoint_nonmember_has_disjoint_member {L : Type*} [Lattice L] [BoundedOrder L]
    (B : Set L) (hB : IsQuasipoint B) (a : L) (ha : a ∉ B) :
    ∃ b ∈ B, b ⊓ a = ⊥ := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P20
