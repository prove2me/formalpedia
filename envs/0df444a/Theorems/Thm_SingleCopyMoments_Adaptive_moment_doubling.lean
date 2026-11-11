-- Prove2me | Theorems.Thm_SingleCopyMoments_Adaptive_moment_doubling
-- name    : SingleCopyMoments.Adaptive.moment_doubling
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T09:46:17.091502+00:00
-- url     : https://prove2.me/theorems/9c33d64c-6b72-45ae-9c56-e889f3b9f94f
-- title:
--   Lemma 24 — Simultaneous moment-order doubling
-- statement:
--   Fix $m\ge2$ and $1/2\le a<1$. Suppose that for every fixed accuracy and failure tolerance the $m$th moment has an adaptive single-copy estimator with worst-case rate $O(d^a)$, uniformly over dimensions and states. Then for every $\varepsilon,\delta\in(0,1)$ one protocol has a measurable vector readout satisfying
--
--   $$T\le C_{m,a,\varepsilon,\delta}d^{1/(2-a)},\qquad\Pr_\rho\{\forall k\in\{m,\ldots,2m\}:|\widehat p_k-p_k(\rho)|\le\varepsilon\}\ge1-\delta.$$
--
--   The bound holds in every positive dimension and for every state, including the finite small dimensions treated in the proof. All recursive copies and failed filters count toward the fixed worst-case budget. The conclusion is simultaneous, with one joint success event.
--
--   Differences from the source:
--   - encoding: finite-dimensional states, measurable experiments, and their expectations → complex Fin d matrices, explicit Born/product measures, and normalized measurable operations; reason: the coordinate and measure conventions preserve every positive dimension and arbitrary rank; probability and integrability assertions are conclusions, not extra premises
--   - reading: the constant is independent of D in a sentence quantifying dimension d → D denotes that same dimension d; reason: the surrounding statement and proof introduce no second dimension
--   - encoding: O bounds and joint estimates in every dimension → Estimable premise and a measurable vector readout over every positive dimension; reason: the proof explicitly covers the finite small dimensions and one joint event
-- source:
--   Zhenhuan Liu, STOC 2027 submission #41 (October 2026), Lemma 24, printed p. 25 (PDF p. 27); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/41.pdf; PDF SHA-256 f19fd65f41a444a79243fa55aab5dfca3db6adb571b06acff78ee49932174fa9.

import Definitions.Def_SingleCopyMoments_Adaptive_Estimation

open scoped Matrix.Norms.L2Operator

namespace SingleCopyMoments.Adaptive

/-- Lemma 24, printed pp.25–26 (PDF pp.27–28); D in the sentence denotes d. -/
theorem moment_doubling (m : ℕ) (hm : 2 ≤ m) (a : ℝ)
    (ha : a ∈ Set.Ico (1/2) 1) (inner : Estimable m a) :
    ∀ ε ∈ Set.Ioo (0 : ℝ) 1, ∀ δ ∈ Set.Ioo (0 : ℝ) 1,
      ∃ C > 0, ∀ d : ℕ, 0 < d → ∃ T : ℕ, ∃ P : Protocol d,
        ∃ out : Record P → ℕ → ℝ,
          (T : ℝ) ≤ C * (d : ℝ) ^ (1/(2-a)) ∧ SimultaneousSucceeds P T m out ε δ := by sorry

end SingleCopyMoments.Adaptive
