-- Prove2me | Theorems.Thm_ProcessingNetworks_GlobalStability_departure_rate_extinction
-- name    : ProcessingNetworks.GlobalStability.departure_rate_extinction
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T18:12:08.453626+00:00
-- url     : https://prove2.me/theorems/00464930-247d-495e-b2d8-66d64b7795c0
-- title:
--   Lemma 8.20 — departure-rate extinction criterion, restated (milestone)
-- statement:
--   **Lemma 8.20.** Fix $\varepsilon > 0$. Assume $(D,F,T,Z)$ is a fluid model solution
--   satisfying (6.1)-(6.6) and $Z_j(t) > 0$ implies $\dot D_j(t) \ge \alpha_j + \varepsilon$
--   (8.31). Then $Z(t) = 0$ for $t \ge |(I-P')^{-1}Z(0)|/\varepsilon$.
--
--   This chunk's page range (PDF 160-175 split as 160-165/164-175 between missions VI and VII)
--   places this lemma's statement at the boundary; `BRIEF.md` lists it as a milestone of this
--   chunk as well as mission VI's, so it is restated here identically (see mission VI's
--   `MODERATION_NOTES.md` for the full discussion) — it is not used by this mission's own goal
--   theorem (8.25 uses Lemma 8.26/8.27's piecewise-linear argument instead), but is included as
--   instructed. The queueing network's data are as in Section 2.6 ($\lambda \ge 0$, $m > 0$,
--   $b > 0$, $P$ substochastic and transient), stated here as explicit hypotheses since this
--   mission's restated `QueueingNetworkData` carries only the raw arrays.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 164, Lemma 8.20

import Mathlib
import Definitions.Def_ProcessingNetworks_GlobalStability_QueueingNetworkData
import Definitions.Def_ProcessingNetworks_GlobalStability_WorkloadOperator

namespace ProcessingNetworks.GlobalStability

open Matrix

/-- Lemma 8.20, Dai & Harrison p. 148 (PDF p. 164), restated from mission VI (this chunk's page
range, PDF 164-175, overlaps mission VI's at page 164, and `BRIEF.md` lists it as a milestone of
this chunk too): fix `ε > 0`. If a fluid model solution `(D,F,T,Z)` of a queueing network
satisfies (6.1)-(6.6) and `Zⱼ(t) > 0` implies `Ḋⱼ(t) ≥ αⱼ + ε` (8.31), then `Z(t) = 0` for
`t ≥ |(I-P')⁻¹Z(0)|/ε`. The queueing network's data are as in Section 2.6: `λ ≥ 0`, `m > 0`,
`b > 0`, and `P` substochastic and transient. -/
theorem departure_rate_extinction
    {I K : ℕ} (dat : QueueingNetworkData I K) (Q : Matrix (Fin I) (Fin I) ℝ)
    (hQ : IsRoutingInverse dat.P Q)
    (hlam : ∀ i, 0 ≤ dat.lam i) (hm : ∀ i, 0 < dat.m i) (hb : ∀ k, 0 < dat.b k)
    (hP_nonneg : ∀ i j, 0 ≤ dat.P i j) (hP_rowsum : ∀ i, ∑ j, dat.P i j ≤ 1)
    (hP_transient : ∀ i j, Filter.Tendsto (fun n => (dat.P ^ n) i j) Filter.atTop (nhds 0))
    (Dh Fh Th Zh : ℝ → Fin I → ℝ) (hsol : IsFluidModelSolutionQN dat Dh Fh Th Zh)
    (ε : ℝ) (hε : 0 < ε)
    (hdrift : ∀ (j : Fin I) (t : ℝ), 0 < t → 0 < Zh t j →
      ∀ d : ℝ, HasDerivAt (fun s => Dh s j) d t → totalArrivalRates dat Q j + ε ≤ d) :
    ∀ t : ℝ, (∑ i, (Q.mulVec (Zh 0)) i) / ε ≤ t → Zh t = fun _ => 0 := by sorry

end ProcessingNetworks.GlobalStability
