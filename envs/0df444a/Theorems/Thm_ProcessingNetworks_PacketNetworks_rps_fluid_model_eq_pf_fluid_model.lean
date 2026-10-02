-- Prove2me | Theorems.Thm_ProcessingNetworks_PacketNetworks_rps_fluid_model_eq_pf_fluid_model
-- name    : ProcessingNetworks.PacketNetworks.rps_fluid_model_eq_pf_fluid_model
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T20:04:10.370643+00:00
-- url     : https://prove2.me/theorems/de69915c-9760-4e2c-9db1-599e5cef3690
-- title:
--   Proposition 12.26 — the RPS fluid model is a special case of the PF fluid model (milestone)
-- statement:
--   **Proposition 12.26.** The RPS fluid model is a special case of the PF fluid model formulated
--   in Section 10.4, with the correspondences: the $I$ packet classes play the role of job
--   classes in the PF fluid model; one demand group per link, so $L=K$; the partition
--   $\{\mathcal I(k), k\in\mathcal K\}$ is defined as in Section 12.6; and it is $\langle
--   C\rangle$ that plays the role of $\tilde{\mathcal A}$ in the concave optimization problem
--   (10.23).
--
--   **Formalization note.** "Special case" is an embedding: under Assumption 12.1, every RPS fluid
--   model solution $(\hat D,\hat T,\hat Z)$ yields the PF fluid model solution
--   $(\hat A,\hat D,\hat D,\hat Z)$ (mission IX's Definition 10.3, imported) at the data
--   `toPFData fr lam`, with unit service times (so PF's $D = T/m = T$) and the PF arrival process
--   $\hat A(t) = \lambda t + P'\hat D(t)$ (10.31). The converse direction is not claimed: a PF
--   fluid model solution carries no schedule-usage components $\hat T_s$, so it does not determine
--   an RPS fluid model solution. Assumption 12.1 makes $R = I - P'$ invertible, which gives
--   $\hat D(0) = 0$ from (12.31).
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 251 (PDF p. 267), Proposition 12.26

import Mathlib
import Definitions.Def_ProcessingNetworks_PacketNetworks_RPSFluidModel

namespace ProcessingNetworks.PacketNetworks

/-- Proposition 12.26, Dai & Harrison p. 251 (PDF p. 267): the RPS fluid model is a special case
of the PF fluid model of Section 10.4, with the correspondences: the `I` packet classes play the
role of job classes; one demand group per link, `L = K`; the partition `{I(k), k ∈ K}` is the link
designation; and `⟨C⟩` plays the role of `Ã` in (10.23). Concretely, under Assumption 12.1, every
RPS fluid model solution `(D̂,T̂,Ẑ)` yields a PF fluid model solution `(Â, D̂, D̂, Ẑ)` at the data
`toPFData fr lam` (unit service times, so PF's `D = T/m = T`), with the PF arrival process
`Â(t) = λt + P'D̂(t)` (10.31). -/
theorem rps_fluid_model_eq_pf_fluid_model
    {I K : ℕ} (fr : FixedRoutingData I K) (h121 : SatisfiesAssumption121 fr.dat)
    (S : Finset (Fin I → ℕ)) (lam : Fin I → ℝ)
    (Dh : ℝ → Fin I → ℝ) (Th : ℝ → (Fin I → ℕ) → ℝ) (Zh : ℝ → Fin I → ℝ)
    (h : IsRPSFluidModelSolution fr S lam Dh Th Zh) :
    ProportionalFairness.IsPFFluidModelSolution (toPFData fr lam)
      (fun t i => lam i * t + ∑ k, RouteMatrix fr k i * Dh t k) Dh Dh Zh := by sorry

end ProcessingNetworks.PacketNetworks
