-- Prove2me | Theorems.Thm_ProcessingNetworks_PacketNetworks_schedule_usage_lipschitz
-- name    : ProcessingNetworks.PacketNetworks.schedule_usage_lipschitz
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T19:51:40.769431+00:00
-- url     : https://prove2.me/theorems/9d63d571-1932-47c4-b6c1-09f7f0b0d948
-- title:
--   Lemma 12.11 — the schedule-usage counting process is Lipschitz (milestone)
-- statement:
--   **Lemma 12.11.** For each $s\in S$ and each $\omega\in\Omega$, $T_s(\tau_2,\omega) -
--   T_s(\tau_1,\omega) \le \tau_2 - \tau_1$ for $\tau_1\le\tau_2$ (Eq. 12.28).
--
--   The book calls this "obvious"; with `Tproc` defined as an indicator count over $\{1,\dots,
--   \tau\}$ of the schedules the policy employs, it is a genuine (if easy) fact about
--   `Finset.card`, not a hypothesis.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 235, Lemma 12.11, Eq. (12.28)

import Mathlib
import Definitions.Def_ProcessingNetworks_PacketNetworks_ProcessesAndFluidModel

namespace ProcessingNetworks.PacketNetworks

/-- Lemma 12.11, Dai & Harrison p. 235 (PDF p. 251): for each schedule `s` and each sample path
`ω`, `Tₛ(·,ω)` is Lipschitz in the stated sense: `Tₛ(τ₂,ω) − Tₛ(τ₁,ω) ≤ τ₂ − τ₁` for `τ₁ ≤ τ₂`
(Eq. 12.28), in the network started from any `z` under the Markovian policy `f`. -/
theorem schedule_usage_lipschitz
    {I J : ℕ} {Ω : Type*} (dat : PacketNetworkData I J) (P : PacketPrimitives I J Ω)
    (z : Fin I → ℕ) (s : Fin J → ℕ) (ω : Ω) (τ1 τ2 : ℕ) (h : τ1 ≤ τ2) :
    Tproc dat P z s τ2 ω - Tproc dat P z s τ1 ω ≤ (τ2 - τ1 : ℝ) := by sorry

end ProcessingNetworks.PacketNetworks
