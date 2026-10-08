-- Prove2me | Theorems.Thm_RossQC_Regions_lemma_2_1
-- name    : RossQC.Regions.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:17:12.520353+00:00
-- url     : https://prove2.me/theorems/d6a42a00-d89b-49c7-a4f8-902f12d7f8d0
-- title:
--   Lemma 2.1 — V_β is a concave function of the belief P
-- statement:
--   In the general model of Ross's §2 (countable states, stochastic transition matrix, bounded costs, $\beta\in(0,1)$), the $\beta$-discounted optimal cost $V_\beta$ is concave on the belief simplex $S$: for $P^1,P^2\in S$ and $\lambda\in[0,1]$,
--   $$
--   V_\beta\big(\lambda P^1+(1-\lambda)P^2\big)\ \ge\ \lambda V_\beta(P^1)+(1-\lambda)V_\beta(P^2).
--   $$
--
--   Concavity is what makes the inspect and revise regions convex (Theorem 2.2).
--
--   **Formalization Note** $V_\beta$ is the limit of value iteration from $V^0=0$.
-- source:
--   Ross, Quality Control under Markovian Deterioration, Management Science 17(9):587–596 (1971), DOI 10.1287/mnsc.17.9.587, p. 589, Lemma 2.1

import Mathlib
import Definitions.Def_RossQC_Regions_Model

namespace RossQC.Regions

/-- Ross, *Quality Control under Markovian Deterioration*, Management Science 17(9):587–596 (1971),
DOI 10.1287/mnsc.17.9.587, p. 589, Lemma 2.1: "`V_β(P)` is a concave function of `P` — i.e. if
`P = λP¹ + (1 − λ)P²`; then `V_β(P) ≧ λV_β(P¹) + (1 − λ)V_β(P²)`."

Under the standing hypotheses of §1–§2 (`Model.Valid`), `V_β` is concave on the belief simplex
`S`. (`ConcaveOn` includes the convexity of `S`.)

**Formalization Note.** `V_β` is the limit of value iteration from `V⁰ = 0` (`Model.Vβ`). -/
theorem lemma_2_1 {ι : Type*} [Countable ι] (M : Model ι) (hM : M.Valid) :
    ConcaveOn ℝ M.simplex M.Vβ := by sorry

end RossQC.Regions
