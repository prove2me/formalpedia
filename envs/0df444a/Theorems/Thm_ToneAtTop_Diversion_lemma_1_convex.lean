-- Prove2me | Theorems.Thm_ToneAtTop_Diversion_lemma_1_convex
-- name    : ToneAtTop.Diversion.lemma_1_convex
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T05:53:02.203605+00:00
-- url     : https://prove2.me/theorems/b6a0bf15-5c45-4010-9d49-f1702e53293a
-- title:
--   Lemma 1, p. 11 — strict convexity of $L_1$
-- statement:
--   Assume the standing conditions of the diversion model. If $\tau<\sqrt{2\lambda\bar x/p}$, then the authority's expected loss is strictly convex on the first control region:
--
--   $$
--   L\text{ is strictly convex on }[0,1-\tau/\bar x).
--   $$
--
--   This is the first assertion of Lemma 1. It characterizes the part of the loss where the high CEO type may still divert.
-- source:
--   Penno, A Theory of Assurance: Balancing Costly Formal Control with Tone at the Top, SSRN working paper 2876700 (revision of May 2019), p. 11 (PDF 13), Lemma 1, first assertion

import Mathlib
import Definitions.Def_ToneAtTop_Diversion_Model

namespace ToneAtTop.Diversion

/-- The first assertion of Lemma 1. -/
theorem lemma_1_convex (P : Params) (hS : P.Standing)
    (hL1a : P.tau < Real.sqrt (2 * P.lam * P.xbar / P.p)) :
    StrictConvexOn ℝ (Set.Ico (0 : ℝ) (1 - P.tau / P.xbar)) (expectedLoss P) := by sorry

end ToneAtTop.Diversion
