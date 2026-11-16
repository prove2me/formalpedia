-- Prove2me | Theorems.Thm_SingleCopyMoments_Adaptive_Supplement_cyclic_overlap_estimation
-- name    : SingleCopyMoments.Adaptive.Supplement.cyclic_overlap_estimation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:40:54.687181+00:00
-- url     : https://prove2.me/theorems/9a440240-a6e4-4ac3-8e8e-199981dacd44
-- title:
--   Theorem 25 — Ordered complex cyclic-overlap upper bound
-- statement:
--   Fix $t\ge2$ and $\epsilon,\delta\in(0,1)$, and put $h=\lceil\log_2t\rceil$. There are $C>0$ and $d_0$, depending only on $t,\epsilon,\delta$, such that in every dimension $d\ge\max(1,d_0)$ one adaptive single-copy protocol works for all ordered input vectors of $t$ unknown states and satisfies
--   $$T\le C d^{h/(h+1)},\qquad
--   \Pr\{|\widehat z-\operatorname{Tr}(\rho_0\cdots\rho_{t-1})|\le\epsilon\}\ge1-\delta.$$
--   Each round measures one fresh copy of a classically chosen source. The budget is total across all sources, includes all failures, and only classical information passes between copies. Readout is complex and the error is its modulus; the input states may repeat. The joint law is normalized and the success event is measurable.
--
--   This is a companion theorem giving the ordered multistate-overlap upper bound, rather than a step in the proof of the goal.
--
--   Differences from the source:
--   - encoding: O or Theta asymptotic copy counts → positive constants and dimension thresholds preceding unknown inputs; reason: Section 5 fixes exactly this quantifier convention; constants have only the stated permitted dependence
--   - encoding: probability of a successful estimate → normalized Born transcript law and measurable additive-success event; reason: makes the operational probability explicit without assuming successful estimation
--   - encoding: classical source choices and ordered complex trace → a measurable source selector with a complex readout and ordered List product; reason: records reconstruct source choices and each transition consumes one original copy; both complex components are retained
-- source:
--   Zhenhuan Liu, STOC 2027 submission #41 (October 2026), Theorem 25, printed p. 27 (PDF p. 29); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/41.pdf

import Definitions.Def_SingleCopyMoments_Adaptive_Supplement_Multisource

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal ComplexOrder Topology Matrix.Norms.L2Operator
set_option autoImplicit false
noncomputable section

namespace SingleCopyMoments.Adaptive.Supplement

/-- Theorem 25, printed p.27 / PDF p.29. -/
theorem cyclic_overlap_estimation (t : ℕ) (ht : 2 ≤ t)
    (ε δ : ℝ) (hε : ε ∈ Set.Ioo (0 : ℝ) 1) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ C > (0 : ℝ), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → 0 < d →
    ∃ T : ℕ, ∃ P : MultiProtocol d t,
      (T : ℝ) ≤ C * (d : ℝ) ^ exponent t ∧ OverlapSucceeds P T ε δ := by sorry

end SingleCopyMoments.Adaptive.Supplement
