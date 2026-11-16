-- Prove2me | Theorems.Thm_SingleCopyMoments_Adaptive_Supplement_partial_transpose_estimation
-- name    : SingleCopyMoments.Adaptive.Supplement.partial_transpose_estimation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:41:58.246203+00:00
-- url     : https://prove2.me/theorems/3c2181aa-3aca-4d8f-9d16-d302e68dab9a
-- title:
--   Theorem 27 — Partial-transpose-moment upper bound
-- statement:
--   Fix integers $t\ge2$, $q\ge1$, and $\epsilon,\delta\in(0,1)$. Set $h=\lceil\log_2t\rceil$. Constants $C>0$ and $d_0$ depend only on $t,q,\epsilon,\delta$. For every pair of positive subsystem dimensions $a,b$ with total dimension $d=ab\ge d_0$ and either $a=q$ or $b=q$, one adaptive single-copy estimator works for every state on $\mathbb C^a\otimes\mathbb C^b$ and satisfies
--   $$T\le C d^{h/(h+1)},\qquad
--   \Pr\{|\widehat z-\operatorname{Tr}[(\rho^{T_A})^t]|\le\epsilon\}\ge1-\delta.$$
--   The transpose is on the first subsystem in the fixed product basis. Its matrix may have negative eigenvalues; neither PPT nor separability is assumed. Both odd and even $t$ and $q=1$ are included. The target is real, its success event measurable, and its Born law normalized. Every original copy is counted, including channel/filter failures.
--
--   This companion theorem preserves the total-dimension rate when either subsystem is fixed.
--
--   Differences from the source:
--   - encoding: O or Theta asymptotic copy counts → positive constants and dimension thresholds preceding unknown inputs; reason: Section 5 fixes exactly this quantifier convention; constants have only the stated permitted dependence
--   - encoding: probability of a successful estimate → normalized Born transcript law and measurable additive-success event; reason: makes the operational probability explicit without assuming successful estimation
--   - encoding: a real trace target → the real part of that trace; reason: the specified Hermitian or alternating-product target has zero imaginary part on every source instance
--   - encoding: a bipartite d-dimensional state with either subsystem of dimension q → positive a,b with d=a*b and a=q or b=q, in the Fin product basis; reason: basis relabeling represents every bipartite instance and preserves partial-transpose traces
-- source:
--   Zhenhuan Liu, STOC 2027 submission #41 (October 2026), Theorem 27, printed p. 29 (PDF p. 31); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/41.pdf

import Definitions.Def_SingleCopyMoments_Adaptive_Supplement_Targets

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal ComplexOrder Topology Matrix.Norms.L2Operator
set_option autoImplicit false
noncomputable section

namespace SingleCopyMoments.Adaptive.Supplement

/-- Theorem 27, printed p.29 / PDF p.31, either fixed subsystem. -/
theorem partial_transpose_estimation (t q : ℕ) (ht : 2 ≤ t) (hq : 1 ≤ q)
    (ε δ : ℝ) (hε : ε ∈ Set.Ioo (0 : ℝ) 1) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ C > (0 : ℝ), ∃ d₀ : ℕ, ∀ a b : ℕ,
    0 < a → 0 < b → d₀ ≤ a*b → (a = q ∨ b = q) →
    ∃ T : ℕ, ∃ P : Protocol (a*b),
      (T : ℝ) ≤ C * ((a*b : ℕ) : ℝ) ^ exponent t ∧
      RealSucceeds P T (partialTransposeMoment a b t) ε δ := by sorry

end SingleCopyMoments.Adaptive.Supplement
