-- Prove2me | Theorems.Thm_ProcessingNetworks_ProportionalFairness_entropy_lyapunov_dini_bound_regular
-- name    : ProcessingNetworks.ProportionalFairness.entropy_lyapunov_dini_bound_regular
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T19:27:10.51538+00:00
-- url     : https://prove2.me/theorems/2e1aa229-e0cb-447a-baae-7132c97a2bea
-- title:
--   Lemma 10.9 — a pointwise Dini-derivative bound at regular points (milestone)
-- statement:
--   **Lemma 10.9.** At each regular point $t > 0$, $D^+\varphi(t) \le \sum_i \dot Z_i(t)
--   \log(\dot D_i(t)/\alpha_i)$ (Eq. 10.41).
--
--   This is the pointwise bound, at differentiability points, that (together with Lemma 10.11's
--   negative-drift bound — the companion chunk's own goal-supporting lemma) supplies the negative
--   drift Lemma 8.11's extinction criterion needs almost everywhere.
--
--   **Formalization note.** Stated under the chapter's standing assumptions — $\tilde{\mathcal A}$
--   an allocation set in the sense of Section 10.1 (`hdom`), $\lambda \ge 0$, $P$ substochastic and
--   transient, and $\alpha > 0$ (every class receives fluid, so that $\log(\dot D_i(t)/\alpha_i)$
--   is meaningful) — which the book's definition (10.38) and its five lemmas presuppose.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 197, Lemma 10.9, Eq. (10.41)

import Mathlib
import Definitions.Def_ProcessingNetworks_ProportionalFairness_FluidModel
import Definitions.Def_ProcessingNetworks_ProportionalFairness_EntropyLyapunov

namespace ProcessingNetworks.ProportionalFairness

/-- Lemma 10.9, Dai & Harrison p. 197 (PDF p. 213): for a PF fluid model solution, at each
regular point `t > 0`, the upper-right Dini derivative of `φ` is bounded by
`∑_i Ż_i(t) log(Ḋ_i(t)/α_i)` (Eq. 10.41). -/
theorem entropy_lyapunov_dini_bound_regular
    {I L : ℕ} (dat : PFUnitaryNetworkData I L)
    (hdom : IsPFDomain dat.TildeAllocSet) (hlam : ∀ i, 0 ≤ dat.lam i)
    (hP_nonneg : ∀ i j, 0 ≤ dat.P i j) (hP_rowsum : ∀ i, ∑ j, dat.P i j ≤ 1)
    (hP_transient : ∀ i j, Filter.Tendsto (fun n => (dat.P ^ n) i j) Filter.atTop (nhds 0)) (alpha : Fin I → ℝ)
    (Ah Dh Th Zh : ℝ → Fin I → ℝ) (hsol : IsPFFluidModelSolution dat Ah Dh Th Zh)
    (halpha : IsTotalArrivalRates dat alpha) (hα : ∀ i, 0 < alpha i)
    (t : ℝ) (ht : 0 < t) (hreg : RegularPoint Ah Dh Th Zh t) :
    diniUpperRight (phi Dh Zh alpha) t ≤
      ((∑ i, deriv (fun s => Zh s i) t * Real.log (deriv (fun s => Dh s i) t / alpha i) : ℝ) :
        EReal) := by sorry

end ProcessingNetworks.ProportionalFairness
