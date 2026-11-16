-- Prove2me | Theorems.Thm_SingleCopyMoments_Adaptive_Supplement_optimal_nonadaptive_complexity
-- name    : SingleCopyMoments.Adaptive.Supplement.optimal_nonadaptive_complexity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:40:28.448937+00:00
-- url     : https://prove2.me/theorems/440e2437-472d-4a5d-a955-7f82f53ecf89
-- title:
--   Theorem 4 — Optimal nonadaptive estimation of state moments
-- statement:
--   Fix any integer $t\ge2$. There is an accuracy threshold $\epsilon_t>0$ such that for every fixed $0<\epsilon\le\epsilon_t$ there are positive constants $c,C$ and a dimension threshold $d_0$ with the following guarantees for every $d\ge\max(1,d_0)$:
--   $$\begin{aligned}
--   &\exists\text{ nonadaptive single-copy estimator using }T\le C d^{1-1/t}
--    \text{ copies, successful on every state};\\
--   &\forall\text{ such estimators successful on every state},\quad T\ge c d^{1-1/t}.
--   \end{aligned}$$
--   Success means additive error at most $\epsilon$ with probability at least $2/3$ under a normalized Born law. Conditioned on an input-independent seed, all POVMs are fixed before outcomes; measurements may differ between rounds and classical postprocessing is arbitrary. Continuous outcome spaces are included. The constants and threshold do not depend on the unknown state or strategy.
--
--   This companion theorem states the complete nonadaptive optimum. The source attributes the matching collision upper bound to [LCQ+26] and proves the lower bound in §7.5; neither direction is omitted.
--
--   Differences from the source:
--   - encoding: O or Theta asymptotic copy counts → positive constants and dimension thresholds preceding unknown inputs; reason: Section 5 fixes exactly this quantifier convention; constants have only the stated permitted dependence
--   - encoding: probability of a successful estimate → normalized Born transcript law and measurable additive-success event; reason: makes the operational probability explicit without assuming successful estimation
-- source:
--   Zhenhuan Liu, STOC 2027 submission #41 (October 2026), Theorem 4, printed p. 4 (PDF p. 6); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/41.pdf

import Definitions.Def_SingleCopyMoments_Adaptive_Supplement_Targets

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal ComplexOrder Topology Matrix.Norms.L2Operator
set_option autoImplicit false
noncomputable section

namespace SingleCopyMoments.Adaptive.Supplement

/-- Theorem 4, printed p.4 / PDF p.6, both optimality directions. -/
theorem optimal_nonadaptive_complexity (t : ℕ) (ht : 2 ≤ t) :
    ∃ ε₀ > (0 : ℝ), ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∃ d₀ : ℕ,
    ∀ d : ℕ, d₀ ≤ d → 0 < d →
      (∃ T : ℕ, ∃ P : Protocol d,
        IncoherentPurity.Adaptive.IsNonadaptive P ∧
        (T : ℝ) ≤ C * (d : ℝ) ^ nonadaptiveExponent t ∧
        AdditiveSucceeds P T t ε (1/3)) ∧
      (∀ (T : ℕ) (P : Protocol d), IncoherentPurity.Adaptive.IsNonadaptive P →
        AdditiveSucceeds P T t ε (1/3) →
        c * (d : ℝ) ^ nonadaptiveExponent t ≤ (T : ℝ)) := by sorry

end SingleCopyMoments.Adaptive.Supplement
