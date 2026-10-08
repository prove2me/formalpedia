-- Prove2me | Theorems.Thm_RossQC_Regions_equation_3
-- name    : RossQC.Regions.equation_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:22:32.593875+00:00
-- url     : https://prove2.me/theorems/b2710fb2-82d2-467a-ab72-5476e32715f9
-- title:
--   §3, (3) — the two-state optimality equation V_β(P) = min{CP + βV_β(TP); I + βPV_β(1) + β(1 − P)V_β(π); R + βV_β(π)}
-- statement:
--   In Ross's two-state production process the good state $0$ turns bad with probability $\pi$ per period and the bad state $1$ stays bad until revised; producing costs $0$ in the good state and $C$ in the bad one, inspecting costs $I$ and revising $R$; and $0<C<I<R$, $0\le\pi\le1$, $0<\beta<1$. Write $P\in[0,1]$ for the probability of the bad state, $V_\beta(P)$ for the optimal discounted cost of the general model at the belief $(1-P,P)$, and $TP=P+\pi-\pi P$. Then for every $P\in[0,1]$,
--   $$
--   V_\beta(P)=\min\{CP+\beta V_\beta(TP);\ I+\beta PV_\beta(1)+\beta(1-P)V_\beta(\pi);\ R+\beta V_\beta(\pi)\}.
--   $$
--
--   This is the specialization of the general optimality equation (1) to two states, and every later argument of §3 runs on it.
--
--   **Formalization Note** $0<C$ is implicit in the paper (the bad state costs $C$, the good state $0$).
-- source:
--   Ross, Quality Control under Markovian Deterioration, Management Science 17(9):587–596 (1971), DOI 10.1287/mnsc.17.9.587, p. 590, §3, (3)

import Mathlib
import Definitions.Def_RossQC_Regions_Model
import Definitions.Def_RossQC_Regions_TwoState

namespace RossQC.Regions

/-- Ross, *Quality Control under Markovian Deterioration*, Management Science 17(9):587–596 (1971),
DOI 10.1287/mnsc.17.9.587, §3, (3), p. 590 (unnumbered statement): in the two-state specialization of
the general model, `TP = P + π − πP` and
`V_β(P) = min{CP + βV_β(TP); I + βPV_β(1) + β(1 − P)V_β(π); R + βV_β(π)}`, `P ∈ [0, 1]`.

Here `V_β(P)` is `V2 β π C I R P`, the general `V_β` of the two-state instance `twoState` at
the belief `(1 − P, P)`.

**Formalization Note.** Standing hypotheses of §3: `0 < β < 1`, `0 ≤ π ≤ 1` (so that `1 − π`,
`π` are transition probabilities) and `C < I < R` ("It shall be assumed throughout that
`C < I < R`"); `0 < C` is implicit in the paper (the bad state costs `C`, the good state `0`).
-/
theorem equation_3 (β π C I R : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1)
    (hC : 0 < C) (hCI : C < I) (hIR : I < R) :
    ∀ P ∈ Set.Icc (0 : ℝ) 1,
      V2 β π C I R P =
        min (rhs3 β π C I R (V2 β π C I R) P .produce)
          (min (rhs3 β π C I R (V2 β π C I R) P .inspect)
            (rhs3 β π C I R (V2 β π C I R) P .revise)) := by sorry

end RossQC.Regions
