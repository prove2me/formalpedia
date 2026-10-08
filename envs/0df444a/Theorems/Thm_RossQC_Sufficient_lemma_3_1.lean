-- Prove2me | Theorems.Thm_RossQC_Sufficient_lemma_3_1
-- name    : RossQC.Sufficient.lemma_3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:40:41.249039+00:00
-- url     : https://prove2.me/theorems/b0eb84c7-5431-4d5d-a683-8efa7321c7ba
-- title:
--   Lemma 3.1 — value is nondecreasing in the bad-state belief
-- statement:
--   In the two-state model with $0<\beta<1$, $0\le\pi\le1$, and $0<C<I<R$, the discounted value is nondecreasing on the belief interval:
--   $$
--   0\le P\le Q\le1\quad\Longrightarrow\quad V_\beta(P)\le V_\beta(Q).
--   $$
--
--   This monotonicity is used in comparing production, inspection and revision across belief levels.
-- source:
--   Ross, Quality Control under Markovian Deterioration, Management Science 17(9):587–596 (1971), DOI 10.1287/mnsc.17.9.587, p. 590, Lemma 3.1

import Definitions.Def_RossQC_Sufficient_Model

namespace RossQC.Sufficient

/-- Ross, Lemma 3.1, p. 590. `V_β(P)` is nondecreasing in the bad-state
probability on the model's belief interval. -/
theorem lemma_3_1 (M : Model)
    (hβ0 : 0 < M.β) (hβ1 : M.β < 1)
    (hπ0 : 0 ≤ M.π) (hπ1 : M.π ≤ 1)
    (hC0 : 0 < M.C) (hCI : M.C < M.I) (hIR : M.I < M.R) :
    MonotoneOn M.value (Set.Icc (0 : ℝ) 1) := by sorry

end RossQC.Sufficient
