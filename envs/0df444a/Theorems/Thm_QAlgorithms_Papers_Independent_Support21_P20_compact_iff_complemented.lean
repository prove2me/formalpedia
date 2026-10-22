-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P20_compact_iff_complemented
-- name    : QAlgorithms.Papers.Independent.Support21.P20.compact_iff_complemented
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T04:55:52.908749+00:00
-- url     : https://prove2.me/theorems/3e66825d-4700-458a-abc8-cf05a760108e
-- title:
--   Compact opens of a Stone locale
-- statement:
--   Let $L$ be a Stone locale, so its frame of opens is coherent and regular. For any open $a\in L$,
--
--   $$a\text{ is compact}\quad\Longleftrightarrow\quad\exists b\in L:\ a\wedge b=0,\ a\vee b=1.$$
--
--   Compactness means that every open cover of $a$ has a finite subcover, including the empty finite family where appropriate. Thus compact opens are exactly clopen elements. The empty locale is allowed.
-- source:
--   Gelfand-type duality for commutative von Neumann algebras, arXiv:2005.05284v3, PDF p. 13, Lemma 2.39

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P20

namespace QAlgorithms.Papers.Independent.Support21.P20

open Set Filter

open scoped NNReal

universe u v

/-- Lemma 2.39, PDF p.13: precisely the complemented opens are compact. -/
theorem compact_iff_complemented (L : Type u) [Order.Frame L]
    (hL : IsStoneLocale L) (a : L) :
    IsCompactElement a ↔ ∃ b : L, IsCompl a b := by sorry

end QAlgorithms.Papers.Independent.Support21.P20
