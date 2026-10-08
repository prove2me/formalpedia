-- Prove2me | Theorems.Thm_RossQC_Regions_lemma_3_2
-- name    : RossQC.Regions.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:22:37.063772+00:00
-- url     : https://prove2.me/theorems/91159e98-3996-4db0-86b1-724e88a4198d
-- title:
--   Lemma 3.2 — every β-optimal policy produces at all P with 0 ≤ P ≤ π
-- statement:
--   In Ross's two-state production process (standing assumptions $0<\beta<1$, $0\le\pi\le1$, $0<C<I<R$), for every $P$ with $0\le P\le\pi$, producing without inspection is strictly better than both alternatives in (3):
--   $$
--   CP+\beta V_\beta(TP)<I+\beta PV_\beta(1)+\beta(1-P)V_\beta(\pi)\quad\text{and}\quad CP+\beta V_\beta(TP)<R+\beta V_\beta(\pi).
--   $$
--   Hence every $\beta$-optimal policy produces at every such $P$.
--
--   This places the lowest threshold of the optimal policy at or above $\pi$.
--
--   **Formalization Note** "Every $\beta$-optimal policy produces at $P$" is stated as "producing is the unique minimizer of the right side of (3) at $P$", since a $\beta$-optimal rule is one that selects a minimizer.
-- source:
--   Ross, Quality Control under Markovian Deterioration, Management Science 17(9):587–596 (1971), DOI 10.1287/mnsc.17.9.587, p. 590, Lemma 3.2

import Mathlib
import Definitions.Def_RossQC_Regions_Model
import Definitions.Def_RossQC_Regions_TwoState

namespace RossQC.Regions

/-- Ross, *Quality Control under Markovian Deterioration*, Management Science 17(9):587–596 (1971),
DOI 10.1287/mnsc.17.9.587, p. 590, Lemma 3.2: "Every β-optimal policy produces at all `P` such that
`0 ≦ P ≦ π`."

In the two-state model, for every `P ∈ [0, π]` producing is the unique minimizer of the right side
of (3): it is strictly cheaper than inspecting and strictly cheaper than revising.

**Formalization Note.** "Every β-optimal policy produces at `P`" is formalized as "produce is the
unique action attaining the minimum in (3) at `P`", since a β-optimal rule is one selecting a
minimizer (p. 588). `V_β(P)` is `V2 β π C I R P`. Standing hypotheses of §3: `0 < β < 1`,
`0 ≤ π ≤ 1`, `C < I < R`, and the implicit `0 < C`. -/
theorem lemma_3_2 (β π C I R : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1)
    (hC : 0 < C) (hCI : C < I) (hIR : I < R) :
    ∀ P ∈ Set.Icc (0 : ℝ) π,
      rhs3 β π C I R (V2 β π C I R) P .produce < rhs3 β π C I R (V2 β π C I R) P .inspect ∧
      rhs3 β π C I R (V2 β π C I R) P .produce < rhs3 β π C I R (V2 β π C I R) P .revise := by sorry

end RossQC.Regions
