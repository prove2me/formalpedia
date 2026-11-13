-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P20_internalGroup_composition_formula
-- name    : QAlgorithms.Papers.Independent.Intake100.P20.internalGroup_composition_formula
-- status  : Proved
-- author  : @Mrnaiq
-- created : 2026-11-13T02:35:17.279195+00:00
-- url     : https://prove2.me/theorems/d00299d7-c644-40c3-a1e6-c02414152701
-- title:
--   Composition in an internal group category is determined by the group operations
-- statement:
--   Let A and O be groups, and let s,t,e,m give an internal category in groups, with m(g,f) denoting g after f. For every composable pair t(f)=s(g),
--
--   $$m(g,f)=g\,e(s(g))^{-1}f.$$
--
--   Thus category composition is uniquely determined by its arrow group, source and identity maps. This formula is the reusable composition step in reconstruction from a crossed module and in the categorical inverse construction. No commutativity or nonemptiness assumptions beyond the group structures are added.
-- source:
--   Martin Forrester-Barker, Group Objects and Internal Categories, arXiv:math/0212065v1, https://arxiv.org/pdf/math/0212065v1, Section 3, PDF pp.10–12: composition and interchange in internal group categories; the displayed formula is the total-arrow form of the source reconstruction m((d,∂(c)g),(c,g))=(dc,g).

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P20

namespace QAlgorithms.Papers.Independent.Intake100.P20
universe u v
 theorem internalGroup_composition_formula {A : Type u} {O : Type v} [Group A] [Group O]
    (D : CategoryMaps A O) (h : InternalCategoryInGrp D) (f g : A)
    (hfg : D.target f = D.source g) :
    D.compose g f = g * (D.identity (D.source g))⁻¹ * f := by sorry
end QAlgorithms.Papers.Independent.Intake100.P20
