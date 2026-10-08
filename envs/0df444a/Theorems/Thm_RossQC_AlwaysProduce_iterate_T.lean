-- Prove2me | Theorems.Thm_RossQC_AlwaysProduce_iterate_T
-- name    : RossQC.AlwaysProduce.iterate_T
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:41:34.032007+00:00
-- url     : https://prove2.me/theorems/b463bb9f-80fc-4193-8cec-6245836f0a66
-- title:
--   §3 — closed form for the iterated belief update
-- statement:
--   In the two-state model with $0<\beta<1$, $0\le\pi\le1$, and $0<C<I<R$, let $T(P)=P+\pi-\pi P$. For every belief $P\in[0,1]$ and integer $n\ge0$,
--
--   $$
--   T^nP=1-(1-P)(1-\pi)^n.
--   $$
--
--   This expresses the probability of the bad state after $n$ successive periods of production without inspection and supplies the terms in the policy-cost series.
--
--   **Formalization Note** The paper displays the formula for $n\ge1$ and sets $T^0P=P$ immediately before it; the same identity at $n=0$ follows from that convention.
-- source:
--   Ross, Quality Control under Markovian Deterioration, Management Science 17(9):587–596 (1971), DOI 10.1287/mnsc.17.9.587, p. 591, §3, unnumbered display immediately before equation (5)

import Mathlib
import Definitions.Def_RossQC_AlwaysProduce_Model

namespace RossQC.AlwaysProduce

/-- Ross, *Quality Control under Markovian Deterioration*, §3, p. 591,
unnumbered display immediately before equation (5). `T⁰P = P`, and the
formula agrees with the paper for every `n ≥ 1` as well. -/
theorem iterate_T (M : Model)
    (hβ0 : 0 < M.β) (hβ1 : M.β < 1)
    (hπ0 : 0 ≤ M.π) (hπ1 : M.π ≤ 1)
    (hC0 : 0 < M.C) (hCI : M.C < M.I) (hIR : M.I < M.R) :
    ∀ (n : ℕ) (P : ℝ), P ∈ Set.Icc (0 : ℝ) 1 →
      (M.T^[n]) P = 1 - (1 - P) * (1 - M.π) ^ n := by sorry

end RossQC.AlwaysProduce
