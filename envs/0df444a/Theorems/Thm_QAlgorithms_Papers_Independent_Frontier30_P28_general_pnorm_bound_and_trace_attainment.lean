-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P28_general_pnorm_bound_and_trace_attainment
-- name    : QAlgorithms.Papers.Independent.Frontier30.P28.general_pnorm_bound_and_trace_attainment
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T17:15:51.605149+00:00
-- url     : https://prove2.me/theorems/8eda725e-d4b6-42d7-8a2a-ba95c25c3e37
-- title:
--   Sharp general Schatten-norm bound and trace-map attainment
-- statement:
--   Let $n,r\ge1$ be integers and $1\le p\le\infty$. Write $M_n$ for the complex $n\times n$ matrices, $\operatorname{tr}$ for the ordinary unnormalized trace, and $\|A\|_p=(\operatorname{tr}|A|^p)^{1/p}$ for finite $p$, with the spectral operator norm at $p=\infty$. For a complex-linear map $T:M_n\to M_r$, let $\|T\|_{p-p}$ be its induced norm on all complex matrices. Every positive trace-preserving such map satisfies
--
--   $$
--   \|T\|_{p-p}\le n^{1-1/p}.
--   $$
--
--   The trace map $\tau:M_n\to\mathbb C$, $\tau(A)=\operatorname{tr}A$, is completely positive and trace preserving and attains equality. Here $1/\infty=0$, so the endpoint bounds are $1$ and $n$.
--
--   This gives the optimal unrestricted bound; attainment is asserted for scalar output, rather than for every fixed output dimension.
--
--   **Formalization Note** The scalar algebra is represented by $M_1$. Induced norms are extended nonnegative suprema of the output norms over the input unit ball; the displayed finite bounds exclude infinite values.
-- source:
--   Contractivity of positive and trace preserving maps under $L_p$ norms, arXiv:math-ph/0601063v1, PDF p. 2, Theorem II.1 and following attainment clause

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P28

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

namespace QAlgorithms.Papers.Independent.Frontier30.P28

open QAlgorithms.Papers.Independent.Information100.P50 (M Lin schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P30 (IsPositiveMap)

open QAlgorithms.Papers.Independent.Dependency50.P26 (TracePreserving)

open QAlgorithms.Papers.Independent.Dependency50.P11 (IsUnital)

/-- Theorem II.1 and its attainment clause, source PDF p.2 (proof p.3).
Dimensions are positive; positivity is sufficient. Sharpness is asserted for
the trace channel to M_1, not for every prescribed output dimension. -/
theorem general_pnorm_bound_and_trace_attainment
    (n r : ℕ) (hn : 0 < n) (hr : 0 < r) (p : ℝ≥0∞) (hp : 1 ≤ p) :
    (∀ T : Lin n r, IsPositiveMap T → TracePreserving T →
      inducedPNorm p T ≤ ENNReal.ofReal (generalBound n p)) ∧
    QAlgorithms.Entanglement.IsCompletelyPositive (traceChannel n) ∧
    TracePreserving (traceChannel n) ∧
    inducedPNorm p (traceChannel n) = ENNReal.ofReal (generalBound n p) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P28

end
