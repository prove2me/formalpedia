-- Prove2me | Theorems.Thm_ProcessingNetworks_ProportionalFairness_departure_rate_positivity_propagates
-- name    : ProcessingNetworks.ProportionalFairness.departure_rate_positivity_propagates
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T19:35:03.1902+00:00
-- url     : https://prove2.me/theorems/fd6f809a-156f-4d0e-bb10-822e1ca98489
-- title:
--   Lemma 10.15 — positivity of the departure rate propagates to every class (milestone)
-- statement:
--   **Lemma 10.15.** Let $t > 0$ be a regular point of $(D,Z)$, and further assume $\dot D_i(t) >
--   0$ for each class $i \in \mathcal I$ with $Z_i(t) > 0$. Then $\dot D_i(t) > 0$ for every class
--   $i \in \mathcal I$.
--
--   This is not tautological: the hypothesis only pins positivity at *occupied* classes; the
--   conclusion extends it to every class, including currently-empty ones, via the routing
--   structure's connectivity (Appendix B.17/Lemma B.9). It is Remark 10.10's justification that
--   Lemma 10.9's bound (mission IX) is well defined at every regular point.
--
--   **Formalization note.** Stated under the chapter's standing assumptions ($\tilde{\mathcal A}$
--   an allocation set, $\lambda \ge 0$, $P$ substochastic and transient) and with every class
--   receiving flow, $\alpha > 0$: without it an isolated empty class with $\lambda_i = 0$ has
--   $\dot D_i(t) = 0$ and the propagation fails, so the assumption is part of the lemma's content.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 204, Lemma 10.15, Eq. (10.70)

import Mathlib
import Definitions.Def_ProcessingNetworks_ProportionalFairness_RestatedFluidModel

namespace ProcessingNetworks.ProportionalFairness

/-- Lemma 10.15, Dai & Harrison p. 204 (PDF p. 220): let `t > 0` be a regular point of `(D,Z)`,
and assume `Ḋ_i(t) > 0` for every class `i` with `Z_i(t) > 0`. Then `Ḋ_i(t) > 0` for *every*
class `i` (Eq. 10.70) — positivity propagates from occupied classes to all classes via the
routing structure's connectivity (Lemma B.9), not merely tautologically restated on the occupied
classes themselves. -/
theorem departure_rate_positivity_propagates
    {I L : ℕ} (dat : PFUnitaryNetworkData I L)
    (hdom : IsPFDomain dat.TildeAllocSet) (hlam : ∀ i, 0 ≤ dat.lam i)
    (hP_nonneg : ∀ i j, 0 ≤ dat.P i j) (hP_rowsum : ∀ i, ∑ j, dat.P i j ≤ 1)
    (hP_transient : ∀ i j, Filter.Tendsto (fun n => (dat.P ^ n) i j) Filter.atTop (nhds 0))
    (alpha : Fin I → ℝ) (halpha : IsTotalArrivalRates dat alpha) (hα : ∀ i, 0 < alpha i)
    (Ah Dh Th Zh : ℝ → Fin I → ℝ) (hsol : IsPFFluidModelSolution dat Ah Dh Th Zh)
    (t : ℝ) (ht : 0 < t) (hreg : RegularPoint Ah Dh Th Zh t)
    (hpos : ∀ i, 0 < Zh t i → 0 < deriv (fun s => Dh s i) t) :
    ∀ i, 0 < deriv (fun s => Dh s i) t := by sorry

end ProcessingNetworks.ProportionalFairness
