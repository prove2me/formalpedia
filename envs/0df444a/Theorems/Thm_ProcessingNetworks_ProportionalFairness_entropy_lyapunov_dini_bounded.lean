-- Prove2me | Theorems.Thm_ProcessingNetworks_ProportionalFairness_entropy_lyapunov_dini_bounded
-- name    : ProcessingNetworks.ProportionalFairness.entropy_lyapunov_dini_bounded
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T19:25:37.843501+00:00
-- url     : https://prove2.me/theorems/5f891d9d-261b-4683-89fd-a1c1efd27245
-- title:
--   Lemma 10.8 — the Dini derivative of φ is bounded above (milestone)
-- statement:
--   **Lemma 10.8.** There is $M > 0$ with $D^+\varphi(t) \le M$ for all $t \ge 0$ (Eq. 10.40).
--
--   This is the uniform-bound half of the machinery Lemma 8.11's extinction criterion (mission V)
--   needs to handle a Lyapunov function that is not itself Lipschitz.
--
--   **Formalization note.** Stated under the chapter's standing assumptions — $\tilde{\mathcal A}$
--   an allocation set in the sense of Section 10.1 (`hdom`), $\lambda \ge 0$, $P$ substochastic and
--   transient, and $\alpha > 0$ (every class receives fluid, so that $\log(\dot D_i(t)/\alpha_i)$
--   is meaningful) — which the book's definition (10.38) and its five lemmas presuppose.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 197, Lemma 10.8, Eq. (10.40)

import Mathlib
import Definitions.Def_ProcessingNetworks_ProportionalFairness_FluidModel
import Definitions.Def_ProcessingNetworks_ProportionalFairness_EntropyLyapunov

namespace ProcessingNetworks.ProportionalFairness

/-- Lemma 10.8, Dai & Harrison p. 197 (PDF p. 213): for a PF fluid model solution, there is a
constant `M > 0` such that the upper-right Dini derivative `D⁺φ(t) ≤ M` for every `t ≥ 0`
(Eq. 10.40). -/
theorem entropy_lyapunov_dini_bounded
    {I L : ℕ} (dat : PFUnitaryNetworkData I L)
    (hdom : IsPFDomain dat.TildeAllocSet) (hlam : ∀ i, 0 ≤ dat.lam i)
    (hP_nonneg : ∀ i j, 0 ≤ dat.P i j) (hP_rowsum : ∀ i, ∑ j, dat.P i j ≤ 1)
    (hP_transient : ∀ i j, Filter.Tendsto (fun n => (dat.P ^ n) i j) Filter.atTop (nhds 0)) (alpha : Fin I → ℝ)
    (Ah Dh Th Zh : ℝ → Fin I → ℝ) (hsol : IsPFFluidModelSolution dat Ah Dh Th Zh)
    (halpha : IsTotalArrivalRates dat alpha) (hα : ∀ i, 0 < alpha i) :
    ∃ M : ℝ, 0 < M ∧ ∀ t : ℝ, 0 ≤ t → diniUpperRight (phi Dh Zh alpha) t ≤ (M : EReal) := by sorry

end ProcessingNetworks.ProportionalFairness
