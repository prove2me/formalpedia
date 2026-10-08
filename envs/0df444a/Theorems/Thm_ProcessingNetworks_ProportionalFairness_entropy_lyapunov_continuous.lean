-- Prove2me | Theorems.Thm_ProcessingNetworks_ProportionalFairness_entropy_lyapunov_continuous
-- name    : ProcessingNetworks.ProportionalFairness.entropy_lyapunov_continuous
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T19:25:08.710754+00:00
-- url     : https://prove2.me/theorems/f76eabf7-c6f7-436a-a5a1-f2b54e9860e5
-- title:
--   Lemma 10.7 — the entropy Lyapunov function is continuous on (0,∞) (milestone, added)
-- statement:
--   **Lemma 10.7.** $\varphi$ is continuous on $(0,\infty)$.
--
--   **Not in `BRIEF.md`'s disposition table for this chunk** — a planning-time omission caught
--   during drafting: the book itself lists Lemma 10.7 as one of the "following five lemmas" (10.6,
--   10.7, 10.8, 10.9, and 10.11) that "suffice to prove Theorem 10.5," on the same page (PDF p.
--   213, printed p. 197) as Lemmas 10.6/10.8/10.9, which *are* in the table. Added here and
--   documented in `HARD.md`/`STATUS.md`, following this series' established convention for such
--   omissions (missions VI/VII's Lemma 8.20).
--
--   **Formalization note.** Stated under the chapter's standing assumptions — $\tilde{\mathcal A}$
--   an allocation set in the sense of Section 10.1 (`hdom`), $\lambda \ge 0$, $P$ substochastic and
--   transient, and $\alpha > 0$ (every class receives fluid, so that $\log(\dot D_i(t)/\alpha_i)$
--   is meaningful) — which the book's definition (10.38) and its five lemmas presuppose.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 197, Lemma 10.7 (added — see natural_language_statement)

import Mathlib
import Definitions.Def_ProcessingNetworks_ProportionalFairness_FluidModel
import Definitions.Def_ProcessingNetworks_ProportionalFairness_EntropyLyapunov

namespace ProcessingNetworks.ProportionalFairness

/-- Lemma 10.7, Dai & Harrison p. 197 (PDF p. 213): for a PF fluid model solution, the entropy
Lyapunov function `φ` is continuous on `(0,∞)`. Not in `BRIEF.md`'s disposition table for this
chunk (a planning-time omission, on the same page as Lemmas 10.6/10.8/10.9 and explicitly one of
the "following five lemmas" the book says suffice to prove Theorem 10.5); added here and
documented in `HARD.md`/`STATUS.md`, per this series' established convention for such omissions
(cf. missions VI/VII's Lemma 8.20). -/
theorem entropy_lyapunov_continuous
    {I L : ℕ} (dat : PFUnitaryNetworkData I L)
    (hdom : IsPFDomain dat.TildeAllocSet) (hlam : ∀ i, 0 ≤ dat.lam i)
    (hP_nonneg : ∀ i j, 0 ≤ dat.P i j) (hP_rowsum : ∀ i, ∑ j, dat.P i j ≤ 1)
    (hP_transient : ∀ i j, Filter.Tendsto (fun n => (dat.P ^ n) i j) Filter.atTop (nhds 0)) (alpha : Fin I → ℝ)
    (Ah Dh Th Zh : ℝ → Fin I → ℝ) (hsol : IsPFFluidModelSolution dat Ah Dh Th Zh)
    (halpha : IsTotalArrivalRates dat alpha) (hα : ∀ i, 0 < alpha i) :
    ContinuousOn (phi Dh Zh alpha) (Set.Ioi 0) := by sorry

end ProcessingNetworks.ProportionalFairness
