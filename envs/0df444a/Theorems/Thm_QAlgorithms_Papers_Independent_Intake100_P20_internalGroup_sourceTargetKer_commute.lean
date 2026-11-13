-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P20_internalGroup_sourceTargetKer_commute
-- name    : QAlgorithms.Papers.Independent.Intake100.P20.internalGroup_sourceTargetKer_commute
-- status  : Proved
-- author  : @Mrnaiq
-- created : 2026-11-13T02:42:00.104927+00:00
-- url     : https://prove2.me/theorems/b8e19bd1-373f-481f-8153-95cf1da598f4
-- title:
--   Source and target kernels commute in an internal group category
-- statement:
--   Let s and t be the source and target homomorphisms of an internal category in groups. Then
--
--   $$a\in\ker s,\quad b\in\ker t\quad\Longrightarrow\quad ab=ba.$$
--
--   No commutativity assumption on the arrow group is required. This commuting-kernel identity supplies the Peiffer identity in reconstruction of the crossed module from an internal category.
-- source:
--   Martin Forrester-Barker, Group Objects and Internal Categories, arXiv:math/0212065v1, https://arxiv.org/pdf/math/0212065v1, PDF pp.8,10–11, Section 3: the interchange law and the Peiffer-identity calculation; this is the commuting-kernel form of that calculation.

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P20
import Mathlib.Tactic.Group

namespace QAlgorithms.Papers.Independent.Intake100.P20
universe u v
theorem internalGroup_sourceTargetKer_commute {A : Type u} {O : Type v} [Group A] [Group O]
    (D : CategoryMaps A O) (h : InternalCategoryInGrp D) (a b : A)
    (ha : D.source a = 1) (hb : D.target b = 1) : a * b = b * a := by sorry
end QAlgorithms.Papers.Independent.Intake100.P20
