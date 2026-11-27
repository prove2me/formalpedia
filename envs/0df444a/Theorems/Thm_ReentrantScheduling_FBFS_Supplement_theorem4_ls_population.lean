-- Prove2me | Theorems.Thm_ReentrantScheduling_FBFS_Supplement_theorem4_ls_population
-- name    : ReentrantScheduling.FBFS.Supplement.theorem4_ls_population
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T13:15:19.92092+00:00
-- url     : https://prove2.me/theorems/86caf244-755f-415a-92fc-4544740f45a0
-- title:
--   Theorem 4 (corrected: positive service times) — uniform LS population bounds
-- statement:
--   Fix a finite reentrant line, nonnegative arrival parameters $\lambda,\gamma$, nonnegative due-date parameters $\gamma_1,\gamma_2$, and an arbitrary fixed nonnegative estimate vector $(\zeta_i)$. Assume $\rho=\lambda\overline w<1$. There exist a finite-valued function $f:\mathbb N\to\mathbb R$ and a finite $\Gamma\ge0$, depending only on those fixed parameters, with the following property. For every nonidling nonpreemptive LS run satisfying (1) and every due-date assignment satisfying $-\gamma_1\le\delta(a)-\alpha(a)\le\gamma_2$ for every part, if $n=x(0)$ then
--
--   $$\sup_{t\ge0}x(t)<f(n),\qquad \limsup_{t\to\infty}x(t)\le\Gamma.$$
--
--   Here $x(t)$ counts every part still in the system, whether waiting or in service. Both $f$ and $\Gamma$ are chosen before the run and the due-date assignment; $\Gamma$ is independent of the initial population. No estimate accuracy or monotonicity is required, and due dates may precede releases. This companion theorem adds population control for due-date-based scheduling alongside the existing FBFS goal. Taking $\zeta_i\equiv0$ gives the paper's Corollary 1 (EDD).
--
--   **Formalization Note** The count $n$ exists for every raw run, since $x(0)$ is the encard of a subset of the finite releases by time zero. Counts and their envelopes retain infinity. LS has no FIFO restriction. Buffers are 0-based. The positive-time pin described below is inherited from the mandated published base model.
--
--   Differences from the source:
--   - correction: Processing times in the printed setting have no explicit strict positivity hypothesis → Every processing time is strictly positive in the required immutable base Line; reason: The brief mandates the published Line and its disclosed positive-time pin; the source busy-period proof divides by a processing time (p. 1409). Zero processing times are excluded, not proved covered here
--   - encoding: Buffers are numbered from 1 and starts are implicit event times → Buffers are 0-based and raw starts and exits lie in WithTop ℝ; reason: Never-served parts retain infinite exit; no service completion is assumed
--   - encoding: The two conclusions use a supremum and limsup of population, with x(0) a finite integer → Both envelopes are in ENNReal and the finite initial count is supplied as n with x(0)=n; reason: Complete-order envelopes avoid a false zero for unbounded real suprema; finite release sets guarantee the count witness
--   - reading: Theorem 4 writes f(x(0)) and says Γ does not depend on x(0) → Finite f and Γ are chosen after fixed line and scalar/vector parameters and before runs and due-date assignments; reason: This makes the initial-population-only bound and initial-state-independent asymptotic bound explicit as required by the structured brief
-- source:
--   Lu & Kumar, Distributed Scheduling Based on Due Dates and Buffer Priorities, IEEE TAC 36(12), 1991, p. 1413, Theorem 4; p. 1408, LS; (1), (3), (16)

import Mathlib
import Definitions.Def_ReentrantScheduling_FBFS_Supplement_LeastSlack

namespace ReentrantScheduling.FBFS.Supplement

/-- Theorem 4, p. 1413: both LS population bounds, uniformly over runs and due dates. -/
theorem theorem4_ls_population (L : Line) (lam γ γ₁ γ₂ : ℝ)
    (hlam : 0 ≤ lam) (hγ : 0 ≤ γ) (hγ₁ : 0 ≤ γ₁) (hγ₂ : 0 ≤ γ₂)
    (hload : L.load lam < 1) (ζ : Fin L.l → ℝ) (hζ : ∀ i, 0 ≤ ζ i) :
    ∃ (f : ℕ → ℝ) (Γ : ℝ), 0 ≤ Γ ∧
      ∀ (R : Run L) (δ : R.Part → ℝ), R.Arrivals lam γ →
        DueWindow R δ γ₁ γ₂ → LSAdmissible R δ ζ →
        ∀ n : ℕ, R.x 0 = (n : ℕ∞) →
          populationSup R < ENNReal.ofReal (f n) ∧
          populationLimsup R ≤ ENNReal.ofReal Γ := by sorry

end ReentrantScheduling.FBFS.Supplement
