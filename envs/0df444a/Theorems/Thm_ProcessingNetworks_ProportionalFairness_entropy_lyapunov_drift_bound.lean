-- Prove2me | Theorems.Thm_ProcessingNetworks_ProportionalFairness_entropy_lyapunov_drift_bound
-- name    : ProcessingNetworks.ProportionalFairness.entropy_lyapunov_drift_bound
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T19:31:42.631647+00:00
-- url     : https://prove2.me/theorems/a998de6a-6c7e-4c57-8cb6-cd46af307dce
-- title:
--   Lemma 10.11 — the entropy Lyapunov function has uniform negative drift under the load condition (milestone)
-- statement:
--   **Lemma 10.11.** Given that the load condition (10.37) holds, there exists $\varepsilon > 0$
--   such that, for each regular point $t > 0$, $Z(t) \ne 0$ implies
--   $$\sum_{i\in\mathcal I} \dot Z_i(t)\log\!\left(\frac{\dot D_i(t)}{\alpha_i}\right) \le
--   -\varepsilon.$$
--
--   This is the uniform negative-drift bound that, together with Lemma 10.9's pointwise Dini bound
--   (mission IX), lets Lemma 8.11's extinction criterion (mission V) conclude that the entropy
--   Lyapunov function reaches $0$ in finite time — the last technical step of Theorem 10.5's proof.
--
--   **Formalization note.** Stated under the chapter's standing assumptions — $\tilde{\mathcal A}$
--   an allocation set in the sense of Section 10.1, $\lambda \ge 0$, $P$ substochastic and
--   transient, $\alpha > 0$ — which the load condition (10.37) and the entropy function (10.38)
--   presuppose.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 197, Lemma 10.11, Eq. (10.42)

import Mathlib
import Definitions.Def_ProcessingNetworks_ProportionalFairness_RestatedFluidModel
import Definitions.Def_ProcessingNetworks_ProportionalFairness_RestatedCore

namespace ProcessingNetworks.ProportionalFairness

/-- Lemma 10.11, Dai & Harrison p. 197 (PDF p. 213): given that the load condition (10.37) holds,
there is `ε > 0` such that, for each regular point `t > 0` with `Z(t) ≠ 0`, the entropy drift
`∑_i Ż_i(t) log(Ḋ_i(t)/α_i) ≤ -ε` (Eq. 10.42). -/
theorem entropy_lyapunov_drift_bound
    {I L : ℕ} (dat : PFUnitaryNetworkData I L)
    (hdom : IsPFDomain dat.TildeAllocSet) (hlam : ∀ i, 0 ≤ dat.lam i)
    (hP_nonneg : ∀ i j, 0 ≤ dat.P i j) (hP_rowsum : ∀ i, ∑ j, dat.P i j ≤ 1)
    (hP_transient : ∀ i j, Filter.Tendsto (fun n => (dat.P ^ n) i j) Filter.atTop (nhds 0))
    (alpha : Fin I → ℝ) (halpha : IsTotalArrivalRates dat alpha) (hα : ∀ i, 0 < alpha i)
    (hload : ∃ a ∈ dat.TildeAllocSet,
      ∀ ℓ, groupAggregate dat.grp (fun i => alpha i * dat.m i) ℓ < a ℓ) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (Ah Dh Th Zh : ℝ → Fin I → ℝ), IsPFFluidModelSolution dat Ah Dh Th Zh →
        ∀ t : ℝ, 0 < t → RegularPoint Ah Dh Th Zh t → Zh t ≠ 0 →
          ∑ i, deriv (fun s => Zh s i) t * Real.log (deriv (fun s => Dh s i) t / alpha i) ≤ -ε := by sorry

end ProcessingNetworks.ProportionalFairness
