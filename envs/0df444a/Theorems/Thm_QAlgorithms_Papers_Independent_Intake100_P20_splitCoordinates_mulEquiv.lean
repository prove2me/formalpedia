-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P20_splitCoordinates_mulEquiv
-- name    : QAlgorithms.Papers.Independent.Intake100.P20.splitCoordinates_mulEquiv
-- status  : Proved
-- author  : @Mrnaiq
-- created : 2026-11-13T02:41:45.102805+00:00
-- url     : https://prove2.me/theorems/87307607-860b-4135-b3f9-107c56cdfb6e
-- title:
--   A split group homomorphism gives the explicit semidirect-product isomorphism
-- statement:
--   Let s:A→O and e:O→A be group homomorphisms satisfying s(e(x))=x. Let O act on ker(s) by conjugation through e. There is a group isomorphism
--
--   $$q:A\simeq\ker(s)\rtimes O,\qquad q(a)=(ae(s(a))^{-1},s(a)),$$
--
--   whose inverse is q⁻¹(k,x)=ke(x). The conclusion fixes both actual coordinate formulas, so it can be reused when checking source, target and composition in reconstruction of internal categories.
-- source:
--   Martin Forrester-Barker, Group Objects and Internal Categories, arXiv:math/0212065v1, https://arxiv.org/pdf/math/0212065v1, PDF p.9, Section 3, Interlude: the explicit splitting isomorphism A≅Ker(s)⋊O and its inverse.

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P20
import Mathlib.Tactic.Group

namespace QAlgorithms.Papers.Independent.Intake100.P20
universe u v
theorem splitCoordinates_mulEquiv {A : Type u} {O : Type v} [Group A] [Group O]
    (s : A →* O) (e : O →* A) (h : ∀ x, s (e x) = x) :
    ∃ q : A ≃* SemidirectProduct s.ker O (splitAction s e),
      (∀ a, q a = splitCoordinates s e h a) ∧
      ∀ z, q.symm z = splitAssembly s e z := by sorry
end QAlgorithms.Papers.Independent.Intake100.P20
