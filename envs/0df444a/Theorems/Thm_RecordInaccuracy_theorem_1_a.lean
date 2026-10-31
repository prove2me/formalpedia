-- Prove2me | Theorems.Thm_RecordInaccuracy_theorem_1_a
-- name    : RecordInaccuracy.theorem_1_a
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:14:40.704878+00:00
-- url     : https://prove2.me/theorems/418bcdbd-e029-47ea-8ce0-129a61b7fca3
-- title:
--   Theorem 1(a) — the belief flow (1) induces the likelihood-ratio order: $\Pi(t_2)\le_{lr}\Pi(t_1)$ for $t_1<t_2$
-- statement:
--   Let $G$ be a shelf inventory distribution, i.e. a belief reachable from the post-restock belief $\mathbb 1_{\{q=q_m\}}$ by the dynamics (1)–(2). Let $\Pi^G(t)$ be the belief $t$ time units after the event that left $G$, with no further observable event (equation (1)). Then for all $0\le t_1<t_2$,
--   $$\Pi^G(t_2)\le_{lr}\Pi^G(t_1),$$
--   that is, $\Pi^G_{q}(t_1)\,\Pi^G_{q'}(t_2)\ge\Pi^G_{q'}(t_1)\,\Pi^G_{q}(t_2)$ for all $q\ge q'$.
--
--   The longer no event is observed, the more the belief shifts toward low stock, in the strongest (likelihood-ratio) sense.
--
--   **Formalization Note** $\le_{lr}$ is `LovejoyPOMDP.Monotone.MLRGE`, written larger argument first.
--
--   Differences from the source:
--   - reading: "$<_{lr}$" → the non-strict likelihood-ratio order $\le_{lr}$ (`MLRGE`); reason: footnote 22 (p.35) defines the order by non-strict cross products, and the proof (16)–(19) shows only non-strict inequalities
--   - reading: $\Pi$ is "the shelf inventory distribution" → a belief reachable from $\mathbb 1_{\{q=q_m\}}$ by (1)–(2) (`Reachable`); reason: the proof (p.35) argues from the restocking belief; for an arbitrary $F=\tfrac12\mathbb 1_{\{q=0\}}+\tfrac12\mathbb 1_{\{q=q_m\}}$ with $q_m\ge 2$ the claim is false
--   - reading: Poisson intensities and probability → $\lambda_D>0$, $\lambda_L,\lambda_P\ge 0$, $\alpha\in[0,1]$ in `Standing`; reason: these are the meanings §2 gives the parameters
--   - encoding: solution of the ODE (1) → normalized matrix exponential $e^{sM}F/\mathbf 1^\top e^{sM}F$; reason: closed linear form of the same solution; differentiating it gives (1)
-- source:
--   Chehrazi, Inventory Systems with Record Inaccuracy, MSOM (2025), doi:10.1287/msom.2023.0274, Theorem 1(a), p.15

import Mathlib
import Definitions.Def_LovejoyPOMDP_Monotone_Orders
import Definitions.Def_RecordInaccuracy_Model

namespace RecordInaccuracy

open LovejoyPOMDP.Monotone

/-- **Theorem 1 (a)** (Likelihood-Ratio Order), Chehrazi, MSOM (2025),
doi:10.1287/msom.2023.0274, p.15: the dynamics (1) induce the likelihood-ratio order — for
`t₁ < t₂`, `Π(t₂) ≤lr Π(t₁)`.

**Formalization Note.** `Π(t) = Π^G(t)` is the belief flow (1) from the shelf inventory
distribution `G` left by the last observable event, i.e. a belief reachable from `1{q = q_m}`
(`Params.Reachable`). The order `≤lr` is `LovejoyPOMDP.Monotone.MLRGE` with the larger belief
first: `Π(t₂) ≤lr Π(t₁)` is `MLRGE (Π t₁) (Π t₂)`. Times are measured from the last event. -/
theorem theorem_1_a (P : Params) (hP : P.Standing) {G : Fin (P.qm + 1) → ℝ}
    (hG : P.Reachable G) {t₁ t₂ : ℝ} (ht₁ : 0 ≤ t₁) (ht : t₁ < t₂) :
    MLRGE (P.flow G t₁) (P.flow G t₂) := by sorry

end RecordInaccuracy
