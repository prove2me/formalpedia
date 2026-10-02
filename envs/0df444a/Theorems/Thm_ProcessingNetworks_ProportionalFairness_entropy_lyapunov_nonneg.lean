-- Prove2me | Theorems.Thm_ProcessingNetworks_ProportionalFairness_entropy_lyapunov_nonneg
-- name    : ProcessingNetworks.ProportionalFairness.entropy_lyapunov_nonneg
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T19:23:59.06272+00:00
-- url     : https://prove2.me/theorems/ad9fc3b6-b8de-4812-80e1-fcf1a5960cd6
-- title:
--   Lemma 10.6 — the entropy Lyapunov function is nonnegative (milestone)
-- statement:
--   **Lemma 10.6.** $\varphi(t) \ge 0$ for all $t \ge 0$; $Z(t) \ne 0 \implies \varphi(t) > 0$.
--
--   This is the positive-definiteness half of showing $\varphi$ is a legitimate Lyapunov function
--   for the extinction criterion (Lemma 8.11, mission V) to apply to.
--
--   **Formalization note.** Stated under the chapter's standing assumptions — $\tilde{\mathcal A}$
--   an allocation set in the sense of Section 10.1 (`hdom`), $\lambda \ge 0$, $P$ substochastic and
--   transient, and $\alpha > 0$ (every class receives fluid, so that $\log(\dot D_i(t)/\alpha_i)$
--   is meaningful) — which the book's definition (10.38) and its five lemmas presuppose.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 197, Lemma 10.6

import Mathlib
import Definitions.Def_ProcessingNetworks_ProportionalFairness_FluidModel
import Definitions.Def_ProcessingNetworks_ProportionalFairness_EntropyLyapunov

namespace ProcessingNetworks.ProportionalFairness

/-- Lemma 10.6, Dai & Harrison p. 197 (PDF p. 213): for a PF fluid model solution, the entropy
Lyapunov function `φ(t) ≥ 0` for every `t ≥ 0`, and `Z(t) ≠ 0` implies `φ(t) > 0`. -/
theorem entropy_lyapunov_nonneg
    {I L : ℕ} (dat : PFUnitaryNetworkData I L)
    (hdom : IsPFDomain dat.TildeAllocSet) (hlam : ∀ i, 0 ≤ dat.lam i)
    (hP_nonneg : ∀ i j, 0 ≤ dat.P i j) (hP_rowsum : ∀ i, ∑ j, dat.P i j ≤ 1)
    (hP_transient : ∀ i j, Filter.Tendsto (fun n => (dat.P ^ n) i j) Filter.atTop (nhds 0)) (alpha : Fin I → ℝ)
    (Ah Dh Th Zh : ℝ → Fin I → ℝ) (hsol : IsPFFluidModelSolution dat Ah Dh Th Zh)
    (halpha : IsTotalArrivalRates dat alpha) (hα : ∀ i, 0 < alpha i) (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ phi Dh Zh alpha t ∧ (Zh t ≠ 0 → 0 < phi Dh Zh alpha t) := by sorry

end ProcessingNetworks.ProportionalFairness
