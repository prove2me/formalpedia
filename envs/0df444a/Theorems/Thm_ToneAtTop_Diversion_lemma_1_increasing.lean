-- Prove2me | Theorems.Thm_ToneAtTop_Diversion_lemma_1_increasing
-- name    : ToneAtTop.Diversion.lemma_1_increasing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:53:09.752254+00:00
-- url     : https://prove2.me/theorems/47895a78-8ffe-4cce-b477-500009d89bb2
-- title:
--   Lemma 1, p. 11 — increasing $L_2$
-- statement:
--   Assume the standing conditions of the diversion model. If $p>1-2\lambda\bar x/\tau^2$, then the authority's expected loss is strictly increasing on the second control region:
--
--   $$
--   c_1<c_2,\quad c_1,c_2\in[1-\tau/\bar x,1)
--   \quad\Longrightarrow\quad L(c_1)<L(c_2).
--   $$
--
--   This is the second assertion of Lemma 1. The lemma says “increasing”; its appendix proof explicitly says “strictly increasing” under this condition.
-- source:
--   Penno, A Theory of Assurance: Balancing Costly Formal Control with Tone at the Top, SSRN working paper 2876700 (revision of May 2019), p. 11 (PDF 13), Lemma 1, second assertion; p. 28 (PDF 30), proof

import Mathlib
import Definitions.Def_ToneAtTop_Diversion_Model

namespace ToneAtTop.Diversion

/-- The second assertion of Lemma 1, strict as in its proof. -/
theorem lemma_1_increasing (P : Params) (hS : P.Standing)
    (hL1b : 1 - 2 * P.lam * P.xbar / P.tau ^ 2 < P.p) :
    StrictMonoOn (expectedLoss P) (Set.Ico (1 - P.tau / P.xbar) 1) := by sorry

end ToneAtTop.Diversion
