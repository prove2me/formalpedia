-- Prove2me | Theorems.Thm_QualityEncroach_FixedCost_footnote_2
-- name    : QualityEncroach.FixedCost.footnote_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:25:05.878767+00:00
-- url     : https://prove2.me/theorems/94d99bcd-ba49-420d-a26e-e57f6e57cc9b
-- title:
--   Footnote 2, p. 37 — negativity of the Hessian numerator
-- statement:
--   Let $h_1(t)=h_{11}(t)+h_{12}(t)\sqrt{20t^2-16t+1}$ be the exact polynomial and square-root expression in footnote 2. For every real $t\ge1$,
--
--   $$h_1(t)<0.$$
--
--   This sign is used in the paper's analysis of interior critical points of the low-direct-quality profit. The polynomials are shared definitions rather than being repeated in this theorem.
-- source:
--   Ha, Long & Nasiry, Quality in Supply Chain Encroachment, authors' manuscript, SSRN 3970373, p. 37, footnote 2

import Mathlib
import Definitions.Def_QualityEncroach_FixedCost_Reduced

namespace QualityEncroach.FixedCost

/-- The sign assertion at the end of footnote 2, p. 37. -/
theorem footnote_2 (t : ℝ) (ht : 1 ≤ t) : h1 t < 0 := by sorry

end QualityEncroach.FixedCost
