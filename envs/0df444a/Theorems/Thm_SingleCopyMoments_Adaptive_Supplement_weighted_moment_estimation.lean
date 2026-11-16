-- Prove2me | Theorems.Thm_SingleCopyMoments_Adaptive_Supplement_weighted_moment_estimation
-- name    : SingleCopyMoments.Adaptive.Supplement.weighted_moment_estimation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:41:30.630049+00:00
-- url     : https://prove2.me/theorems/6e336664-cfbf-4f42-8221-0707a19f2baa
-- title:
--   Theorem 26 — Weighted-moment upper bound
-- statement:
--   Fix $t\ge2$ and $\epsilon,\delta\in(0,1)$, and set $h=\lceil\log_2t\rceil$. Constants $C>0$ and $d_0$ can be chosen depending only on these parameters. For every $d\ge\max(1,d_0)$ and every known Hermitian $O$ with $\|O\|_{\mathrm{op}}\le1$, an adaptive single-copy protocol chosen from $O$ works for every unknown $d$-dimensional state $\rho$ and satisfies
--   $$T\le C d^{h/(h+1)},\qquad
--   \Pr\{|\widehat z-\operatorname{Tr}(O\rho^t)|\le\epsilon\}\ge1-\delta.$$
--   The trace is real. The constants are uniform over $O$ and $\rho$. Negative and zero eigenvalues of $O$ are allowed; no commutativity assumption is made. The law is normalized, success measurable, and all original copies including failed filters count in $T$.
--
--   This companion theorem gives the upper bound for weighted moments. It does not assert a lower bound for each individual observable.
--
--   Differences from the source:
--   - encoding: O or Theta asymptotic copy counts → positive constants and dimension thresholds preceding unknown inputs; reason: Section 5 fixes exactly this quantifier convention; constants have only the stated permitted dependence
--   - encoding: probability of a successful estimate → normalized Born transcript law and measurable additive-success event; reason: makes the operational probability explicit without assuming successful estimation
--   - encoding: a real trace target → the real part of that trace; reason: the specified Hermitian or alternating-product target has zero imaginary part on every source instance
-- source:
--   Zhenhuan Liu, STOC 2027 submission #41 (October 2026), Theorem 26, printed p. 28 (PDF p. 30); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/41.pdf

import Definitions.Def_SingleCopyMoments_Adaptive_Supplement_Targets

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal ComplexOrder Topology Matrix.Norms.L2Operator
set_option autoImplicit false
noncomputable section

namespace SingleCopyMoments.Adaptive.Supplement

/-- Theorem 26, printed p.28 / PDF p.30; C and d₀ precede the known observable. -/
theorem weighted_moment_estimation (t : ℕ) (ht : 2 ≤ t)
    (ε δ : ℝ) (hε : ε ∈ Set.Ioo (0 : ℝ) 1) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ C > (0 : ℝ), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → 0 < d →
    ∀ O : Op d, O.IsHermitian → opNorm O ≤ 1 →
    ∃ T : ℕ, ∃ P : Protocol d,
      (T : ℝ) ≤ C * (d : ℝ) ^ exponent t ∧
      RealSucceeds P T (weightedMoment O t) ε δ := by sorry

end SingleCopyMoments.Adaptive.Supplement
