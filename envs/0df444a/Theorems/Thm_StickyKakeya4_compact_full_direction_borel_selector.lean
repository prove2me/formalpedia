-- Prove2me | Theorems.Thm_StickyKakeya4_compact_full_direction_borel_selector
-- name    : StickyKakeya4.compact_full_direction_borel_selector
-- status  : Open
-- author  : @sensei
-- created : 2026-09-27T12:48:07.773817+00:00
-- url     : https://prove2.me/theorems/00b183ee-23c3-4a54-8e73-3da4afb5d0d3
-- title:
--   Borel selector for a compact full-direction marked-line family
-- statement:
--   Let $\mathcal L$ be a compact family of marked oriented lines in $\mathbb R^4$. Assume every unit direction occurs in $\mathcal L$. Then there is a Borel subfamily $\Gamma\subseteq\mathcal L$ meeting every unit-direction fibre in exactly one marked line: $$\Gamma\subseteq\mathcal L,\qquad \#\{\ell\in\Gamma:\operatorname{dir}(\ell)=\theta\}=1\quad(\theta\in S^3).$$ This is the measurable-uniformization component of the selector reduction. It retains the affine mark because the selected objects are marked lines, not merely unmarked carriers.
-- source:
--   Chenxi Cai, Sticky Kakeya in R4 via contact-symplectic reformulation, Proposition 3.1 (Borel selector reduction), proof paragraph beginning “The compact fibre relation over the Polish base S^3 has a Borel selector”, https://cchx0000.github.io/papers/sticky-kakeya-contact-symplectic/sticky-kakeya-contact-symplectic.pdf

import Definitions.Def_sticky_kakeya4_core

open MeasureTheory Set

namespace StickyKakeya4

theorem compact_full_direction_borel_selector (lines : Set MarkedLine)
    (hcompact : IsCompact lines) (hfull : FullDirection lines) :
    ∃ selector : Set MarkedLine,
      MeasurableSet selector ∧ selector ⊆ lines ∧
      IsDirectionSelector selector := by sorry

end StickyKakeya4
