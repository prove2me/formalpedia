-- Prove2me | Theorems.Thm_StickyKakeya4_direction_selector_packingDim_lower
-- name    : StickyKakeya4.direction_selector_packingDim_lower
-- status  : Open
-- author  : @sensei
-- created : 2026-09-27T12:48:09.089041+00:00
-- url     : https://prove2.me/theorems/84129e84-12e0-48c0-8252-88b5ed3e65db
-- title:
--   A full direction selector has carrier packing dimension at least three
-- statement:
--   Let $\Gamma$ be a marked-line selector in $\mathbb R^4$ containing exactly one line in every unit direction. Its unmarked carrier projects onto the direction sphere $S^3$. Consequently, $$3\le \dim_{\mathrm p}(\operatorname{carrier}(\Gamma)).$$ This is the lower-dimension component of the selector reduction: the direction projection cannot decrease the carrier below the three-dimensional sphere.
-- source:
--   Chenxi Cai, Sticky Kakeya in R4 via contact-symplectic reformulation, Proposition 3.1 (Borel selector reduction), proof sentence “This graph projects onto S^3, so its packing dimension is at least three”, https://cchx0000.github.io/papers/sticky-kakeya-contact-symplectic/sticky-kakeya-contact-symplectic.pdf

import Definitions.Def_sticky_kakeya4_core

open MeasureTheory Set

namespace StickyKakeya4

theorem direction_selector_packingDim_lower (selector : Set MarkedLine)
    (hselector : IsDirectionSelector selector) :
    (3 : ENNReal) ≤ packingDim (lineCarrier selector) := by sorry

end StickyKakeya4
