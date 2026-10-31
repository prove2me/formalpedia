-- Prove2me | Theorems.Thm_RecordInaccuracy_theorem_1_b
-- name    : RecordInaccuracy.theorem_1_b
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:14:45.371082+00:00
-- url     : https://prove2.me/theorems/585b9979-ba12-459f-9783-30a154b22840
-- title:
--   Theorem 1(b) — the dynamics (1)–(2) preserve the likelihood-ratio order
-- statement:
--   Let $G$ and $G'$ be shelf inventory distributions (beliefs reachable from $\mathbb 1_{\{q=q_m\}}$ by (1)–(2)) with
--   $$G'\le_{lr}G .$$
--   Suppose that from this time on both beliefs observe the same history: observable events after gaps $d_1,\dots,d_k\ge 0$, then $t\ge 0$ further time units without an event. Each belief follows the flow (1) between events and the Bayes jump (2) at each event. Then the two resulting beliefs satisfy
--   $$\Pi'(t)\le_{lr}\Pi(t).$$
--
--   Observing the same sequence of events in two scenarios does not change how the two scenarios compare.
--
--   **Formalization Note** The belief after a history is `Params.path G [d_1, …, d_k] t`. $\le_{lr}$ is `MLRGE`, larger argument first.
--
--   Differences from the source:
--   - reading: "$<_{lr}$" → the non-strict likelihood-ratio order $\le_{lr}$ (`MLRGE`); reason: footnote 22 (p.35) defines the order by non-strict cross products
--   - reading: $\Pi,\Pi'$ are shelf inventory distributions under "the dynamics (1)–(2)" → reachable $G,G'$ followed along a common history (gaps $d_i\ge0$, elapsed $t\ge0$); reason: the theorem compares the two beliefs under the same observed events (p.15, "observing the same sequence of events in two different scenarios")
--   - reading: Poisson intensities and probability → $\lambda_D>0$, $\lambda_L,\lambda_P\ge 0$, $\alpha\in[0,1]$ in `Standing`; reason: these are the meanings §2 gives the parameters
--   - encoding: solution of the ODE (1) → normalized matrix exponential; jump at a belief with $h=0$ → Lean's $0/0=0$ vector; reason: closed linear form of the same solution; an event at $h=0$ has probability zero, and there both sides become $0$, where `MLRGE` holds trivially
-- source:
--   Chehrazi, Inventory Systems with Record Inaccuracy, MSOM (2025), doi:10.1287/msom.2023.0274, Theorem 1(b), p.15

import Mathlib
import Definitions.Def_LovejoyPOMDP_Monotone_Orders
import Definitions.Def_RecordInaccuracy_Model

namespace RecordInaccuracy

open LovejoyPOMDP.Monotone

/-- **Theorem 1 (b)** (Likelihood-Ratio Order), Chehrazi, MSOM (2025),
doi:10.1287/msom.2023.0274, p.15: the dynamics (1)–(2) preserve the likelihood-ratio order — if
`Π'(t₀) ≤lr Π(t₀)` then `Π'(t) ≤lr Π(t)` for every `t ≥ t₀`.

**Formalization Note.** `G = Π(t₀)` and `G' = Π'(t₀)` are shelf inventory distributions
(`Params.Reachable`). After `t₀` both beliefs see the same observable events: gaps `ds` between
consecutive events and elapsed time `t` since the last one, so that `Π(t₀ + Σ ds + t) =
P.path G ds t` (`Params.path`: flow (1), jump (2), …, flow (1)). `Π' ≤lr Π` is
`MLRGE Π Π'` (larger first). -/
theorem theorem_1_b (P : Params) (hP : P.Standing) {G G' : Fin (P.qm + 1) → ℝ}
    (hG : P.Reachable G) (hG' : P.Reachable G') (hGG' : MLRGE G G')
    (ds : List ℝ) (hds : ∀ d ∈ ds, 0 ≤ d) {t : ℝ} (ht : 0 ≤ t) :
    MLRGE (P.path G ds t) (P.path G' ds t) := by sorry

end RecordInaccuracy
