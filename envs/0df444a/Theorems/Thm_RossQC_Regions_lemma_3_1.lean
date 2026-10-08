-- Prove2me | Theorems.Thm_RossQC_Regions_lemma_3_1
-- name    : RossQC.Regions.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:22:27.011975+00:00
-- url     : https://prove2.me/theorems/5a914f42-b6d3-4117-af29-67869d6e01d1
-- title:
--   Lemma 3.1 — in the two-state model V_β(P) is monotone nondecreasing in P
-- statement:
--   In Ross's two-state production process (standing assumptions $0<\beta<1$, $0\le\pi\le1$, $0<C<I<R$), the optimal discounted cost $V_\beta(P)$, as a function of the probability $P$ of the bad state, is monotone nondecreasing on $[0,1]$:
--   $$
--   0\le P\le P'\le 1\ \Longrightarrow\ V_\beta(P)\le V_\beta(P').
--   $$
--
--   Monotonicity, with (3), shows that the revise region is a right-hand interval of $[0,1]$, and it drives the comparisons in Lemma 3.2.
--
--   **Formalization Note** $V_\beta(P)$ is the general $V_\beta$ at the belief $(1-P,P)$.
-- source:
--   Ross, Quality Control under Markovian Deterioration, Management Science 17(9):587–596 (1971), DOI 10.1287/mnsc.17.9.587, p. 590, Lemma 3.1

import Mathlib
import Definitions.Def_RossQC_Regions_Model
import Definitions.Def_RossQC_Regions_TwoState

namespace RossQC.Regions

/-- Ross, *Quality Control under Markovian Deterioration*, Management Science 17(9):587–596 (1971),
DOI 10.1287/mnsc.17.9.587, p. 590, Lemma 3.1: "`V_β(P)` is monotone nondecreasing in `P`."

In the two-state model, `P ↦ V_β(P)` is monotone nondecreasing on `[0, 1]`.

**Formalization Note.** `V_β(P)` is `V2 β π C I R P`, the general `V_β` (limit of value iteration
from `V⁰ = 0`) of the two-state instance at the belief `(1 − P, P)`. Standing hypotheses of §3:
`0 < β < 1`, `0 ≤ π ≤ 1`, `C < I < R`, and the implicit `0 < C`. -/
theorem lemma_3_1 (β π C I R : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1)
    (hC : 0 < C) (hCI : C < I) (hIR : I < R) :
    MonotoneOn (V2 β π C I R) (Set.Icc 0 1) := by sorry

end RossQC.Regions
