-- Prove2me | Theorems.Thm_ProcessingNetworks_PacketNetworks_back_pressure_optimal_nonzero
-- name    : ProcessingNetworks.PacketNetworks.back_pressure_optimal_nonzero
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T19:55:51.728137+00:00
-- url     : https://prove2.me/theorems/d6bcf422-a34c-421f-afc7-5a3f4866c29c
-- title:
--   Lemma 12.17 — the MW/BP optimum is nonzero at a nonempty state (milestone)
-- statement:
--   **Lemma 12.17.** For any $z\in\mathbb Z^I_+$ with $z\ne 0$, the optimization problem (12.41)
--   has a solution $s\ne 0$.
--
--   The book's proof exhibits an explicit feasible schedule with positive objective via the largest
--   buffer's hop count (the length of its shortest processing plan to exit), by induction along
--   that plan when the largest buffer's own direct successor is not itself maximal.
--
--   **Formalization note.** The proof uses that a single transfer on any one activity is a
--   feasible schedule ("clearly, $s\in S(z)$"); that is the chapter's standing structure of
--   Section 12.2, $S$ derived from the link configurations via (12.10) under Assumption 12.4,
--   carried as hypotheses. With an arbitrary schedule set (say $S=\{0\}$) the statement fails.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 240, Lemma 12.17

import Mathlib
import Definitions.Def_ProcessingNetworks_PacketNetworks_BackPressurePolicy
import Definitions.Def_ProcessingNetworks_PacketNetworks_SchedulesAndConfigurations

namespace ProcessingNetworks.PacketNetworks

/-- Lemma 12.17, Dai & Harrison p. 240 (PDF p. 256): in a packet network satisfying Assumption
12.1, with schedule set `S` derived from the link configurations via (12.10) under Assumption
12.4 (the chapter's standing structure, which is what makes a single transfer on any activity a
feasible schedule, as the proof uses), for any `z ∈ Z^I_+` with `z ≠ 0` the optimization problem
(12.41) has a solution `s ≠ 0`. -/
theorem back_pressure_optimal_nonzero
    {I J K : ℕ} (dat : PacketNetworkData I J) (h121 : SatisfiesAssumption121 dat)
    (cfg : LinkConfigData J K) (h124 : SatisfiesAssumption124 cfg)
    (S : Finset (Fin J → ℕ)) (hS : IsScheduleSet cfg S)
    (z : Fin I → ℕ) (hz : z ≠ 0) :
    ∃ s, IsBPOptimal dat S (fun i => (z i : ℝ)) s ∧ s ≠ 0 := by sorry

end ProcessingNetworks.PacketNetworks
