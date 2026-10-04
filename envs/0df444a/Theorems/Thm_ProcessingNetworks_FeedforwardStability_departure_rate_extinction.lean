-- Prove2me | Theorems.Thm_ProcessingNetworks_FeedforwardStability_departure_rate_extinction
-- name    : ProcessingNetworks.FeedforwardStability.departure_rate_extinction
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T18:07:22.851846+00:00
-- url     : https://prove2.me/theorems/68dc4858-d3be-4a4b-8f23-e5b08def9c3f
-- title:
--   Lemma 8.20 — departure-rate extinction criterion (milestone, added)
-- statement:
--   **Lemma 8.20.** Fix $\varepsilon > 0$. Assume $(D,F,T,Z)$ is a fluid model solution
--   satisfying (6.1)-(6.6) and $Z_j(t) > 0$ implies $\dot D_j(t) \ge \alpha_j + \varepsilon$
--   (8.31). Then $Z(t) = 0$ for $t \ge |(I-P')^{-1}Z(0)|/\varepsilon$.
--
--   This is the structural engine behind Theorem 8.18: it shows that a *uniform excess departure
--   rate over the total arrival rate*, at every non-empty class, is already enough to force
--   extinction, via the linear Lyapunov function $f(t) = e'(I-P')^{-1}Z(t)$ (the total number of
--   services still required anywhere in the network) and Lemma 8.5. Theorem 8.18's proof verifies
--   (8.31) holds for the HLSPS policy specifically, then invokes this lemma directly.
--
--   **Formalization note.** This lemma is numbered (Lemma 8.20) and falls within this chunk's
--   assigned page range (PDF 160-165, Lemma 8.20 is on PDF p. 164) but is not listed in
--   `BRIEF.md`'s disposition table — an evident planning omission, since it is the load-bearing
--   structural step Theorem 8.18's own proof cites by name ("the theorem follows from Lemma
--   8.20"). Per `CAPTAIN_BRIEF.md` rule 9 (disposition changes must be documented, not silent)
--   and the planning brief's "account for every numbered result," it is added here as a milestone
--   — see `STATUS.md` for the explicit record of this addition. $\alpha$ is `totalArrivalRates`,
--   already defined for Lemma 8.15/Theorem 8.18; the conclusion's norm
--   $|(I-P')^{-1}Z(0)|$ is $\sum_i (Q Z(0))_i$, matching the book's own $|\cdot|$-as-sum
--   convention (established at (6.37)) applied to the nonnegative vector $Q Z(0) = (I-P')^{-1}Z(0)$.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 164, Lemma 8.20

import Mathlib
import Definitions.Def_ProcessingNetworks_FeedforwardStability_QueueingNetworkData
import Definitions.Def_ProcessingNetworks_FeedforwardStability_WorkloadOperator

namespace ProcessingNetworks.FeedforwardStability

open Matrix

/-- Lemma 8.20, Dai & Harrison p. 148 (PDF p. 164) (not listed in `BRIEF.md`'s disposition table
but numbered and within this chunk's page range — added as a milestone, see `STATUS.md`): fix
`ε > 0`. If a fluid model solution `(D,F,T,Z)` of a queueing network satisfies (6.1)-(6.6) and
`Zⱼ(t) > 0` implies `Ḋⱼ(t) ≥ αⱼ + ε` (8.31), then `Z(t) = 0` for
`t ≥ |(I-P')⁻¹Z(0)|/ε`. This is the key structural lemma behind Theorem 8.18's proof. -/
theorem departure_rate_extinction
    {I K : ℕ} (dat : QueueingNetworkData I K) (Q : Matrix (Fin I) (Fin I) ℝ)
    (hQ : IsRoutingInverse dat.P Q)
    (Dh Fh Th Zh : ℝ → Fin I → ℝ) (hsol : IsFluidModelSolutionQN dat Dh Fh Th Zh)
    (ε : ℝ) (hε : 0 < ε)
    (hdrift : ∀ (j : Fin I) (t : ℝ), 0 < t → 0 < Zh t j →
      ∀ d : ℝ, HasDerivAt (fun s => Dh s j) d t → totalArrivalRates dat Q j + ε ≤ d) :
    ∀ t : ℝ, (∑ i, (Q.mulVec (Zh 0)) i) / ε ≤ t → Zh t = fun _ => 0 := by sorry

end ProcessingNetworks.FeedforwardStability
