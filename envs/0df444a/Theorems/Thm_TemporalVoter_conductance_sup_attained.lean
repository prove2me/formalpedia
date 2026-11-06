-- Prove2me | Theorems.Thm_TemporalVoter_conductance_sup_attained
-- name    : TemporalVoter.conductance_sup_attained
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:11:52.308233+00:00
-- url     : https://prove2.me/theorems/31815204-a8d5-475e-8bb8-b17afa61f6e3
-- title:
--   §1.3 — the supremum of $\phi^\Delta(\mathcal G)/\Delta$ over $\Delta\ge1$ is attained
-- statement:
--   Let $\mathcal G$ be a temporal graph with fixed degrees. The supremum of $\Delta\mapsto\phi^{\Delta}(\mathcal G)/\Delta$ over integers $\Delta\ge1$ is attained: there is $\Delta^*\ge1$ with
--   $$\Phi(\mathcal G)=\frac{\phi^{\Delta^*}(\mathcal G)}{\Delta^*}.$$
--
--   This makes the temporal conductance a maximum, as written in (5); the proof of Main Theorem 1 uses the maximising window length.
--
--   Differences from the source:
--   - encoding: Φ(G) := max_{Δ≥1} φ^Δ(G)/Δ → temporalConductance = ⨆ over Δ ≥ 1 in ℝ; the statement asserts the supremum equals the value at some Δ* ≥ 1; reason: the paper defines Φ as a maximum after arguing attainment; the supremum of values in [0, 1] is the same number (paper.md R5)
--   - encoding: a sequence of undirected graphs on a common vertex set V(G) with common degree d(v) → T : TemporalGraph V: a Fintype V, G t : SimpleGraph V, and the degree data d with degree_eq and one_le_d; reason: the paper's graphs are plain finite graphs (n vertices, m = ½ ∑ d(v) edges, e_t counts edges); no loop or parallel edge occurs in them, the self-loop of Figure 1 only pictures laziness
-- source:
--   Rocha Avila, Dell, Lapinskas, Temporal Conductance and Bounds on the Voter Model for Dynamic Networks, arXiv:2606.13374 (2 Nov 2026), §1.3, before (5), p.6

import Mathlib
import Definitions.Def_TemporalVoter_temporalConductance

namespace TemporalVoter

/-- **The supremum in (5) is attained** (arXiv:2606.13374, version of 2 Nov 2026, §1.3, p.6): for
every temporal graph with fixed degrees, the supremum of `Δ ↦ φ^Δ(G)/Δ` over integers `Δ ≥ 1` is
attained at some `Δ* ≥ 1`, so `Φ(G) = φ^{Δ*}(G)/Δ*` is a maximum. -/
theorem conductance_sup_attained {V : Type} [Fintype V] (T : TemporalGraph V) :
    ∃ Δ : ℕ, 1 ≤ Δ ∧ temporalConductance T = windowCond T Δ / (Δ : ℝ) := by sorry

end TemporalVoter
