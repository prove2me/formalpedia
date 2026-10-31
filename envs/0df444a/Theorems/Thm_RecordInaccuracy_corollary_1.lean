-- Prove2me | Theorems.Thm_RecordInaccuracy_corollary_1
-- name    : RecordInaccuracy.corollary_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:14:52.907766+00:00
-- url     : https://prove2.me/theorems/792df335-5de3-4dcf-98fc-091c4152fa14
-- title:
--   Corollary 1 — a later $j$-th observed event gives a likelihood-ratio smaller belief
-- statement:
--   Fix the timing of the past $j-1$ observed changes in the inventory record, and let $G=\Pi(\iota_{j-1})$ be the shelf inventory distribution right after the $(j-1)$-th of them. For $j=1$ this is $\mathbb 1_{\{q=q_m\}}$ at the last restocking. If the $j$-th event happens $a$ time units later, the belief becomes $\Pi(\iota_j)=J(\Pi^G(a))$ by (1)–(2). For $0\le a<b$ at which an observable event can occur, i.e. $h(\Pi^G(a))>0$ and $h(\Pi^G(b))>0$,
--   $$J\big(\Pi^G(b)\big)\le_{lr}J\big(\Pi^G(a)\big).$$
--   In the paper's notation: for any $\iota_j<\iota'_j$, $\Pi(\iota'_j)\le_{lr}\Pi(\iota_j)$.
--
--   This bounds the number of observable events after which immediate restocking is optimal.
--
--   **Formalization Note** $\le_{lr}$ is `MLRGE`, larger argument first.
--
--   Differences from the source:
--   - reading: "$<_{lr}$" → the non-strict likelihood-ratio order $\le_{lr}$ (`MLRGE`); reason: footnote 22 (p.35) defines the order by non-strict cross products
--   - reading: $\Pi(\iota_{j-1})$ is a shelf inventory distribution → `Reachable G`; reason: the proof applies Theorem 1(a), which is stated for shelf inventory distributions
--   - reading: Poisson intensities and probability → $\lambda_D>0$, $\lambda_L,\lambda_P\ge 0$, $\alpha\in[0,1]$ in `Standing`; reason: these are the meanings §2 gives the parameters
--   - encoding: event times $\iota_j<\iota'_j$ → offsets $0\le a<b$ from $\iota_{j-1}$ with $h>0$ at both; reason: $\iota_j$ is an event time, so the event intensity there is positive; the guard excludes the $0/0$ of (2)
-- source:
--   Chehrazi, Inventory Systems with Record Inaccuracy, MSOM (2025), doi:10.1287/msom.2023.0274, Corollary 1, p.15

import Mathlib
import Definitions.Def_LovejoyPOMDP_Monotone_Orders
import Definitions.Def_RecordInaccuracy_Model

namespace RecordInaccuracy

open LovejoyPOMDP.Monotone

/-- **Corollary 1**, Chehrazi, MSOM (2025), doi:10.1287/msom.2023.0274, p.15: fixing the timing of
the past `j − 1` observed changes in the inventory record, for any `ι_j < ι'_j`,
`Π(ι'_j) ≤lr Π(ι_j)`.

**Formalization Note.** `G = Π(ι_{j−1})` is the shelf inventory distribution right after the
`(j−1)`-th event (`Params.Reachable`; for `j = 1` it is `1{q = q_m}` at the last restocking).
With `a = ι_j − ι_{j−1}` and `b = ι'_j − ι_{j−1}`, `Π(ι_j) = J(Π^G(a))` by (1)–(2), and likewise
for `b`. The hypotheses `0 < h(Π^G(a))`, `0 < h(Π^G(b))` say that an observable event can occur at
those times (otherwise (2) is `0/0`). `≤lr` is `MLRGE`, larger first. -/
theorem corollary_1 (P : Params) (hP : P.Standing) {G : Fin (P.qm + 1) → ℝ}
    (hG : P.Reachable G) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hha : 0 < P.hazard (P.flow G a)) (hhb : 0 < P.hazard (P.flow G b)) :
    MLRGE (P.jump (P.flow G a)) (P.jump (P.flow G b)) := by sorry

end RecordInaccuracy
