-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P28_trace_norm_contraction
-- name    : QAlgorithms.Papers.Independent.Frontier30.P28.trace_norm_contraction
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T17:16:30.317857+00:00
-- url     : https://prove2.me/theorems/8bb4c9cc-a43f-4b09-aba3-f0d9d276d1df
-- title:
--   Positive trace-preserving maps have trace norm one and contract every matrix
-- statement:
--   Let $n,r\ge1$ and let $T:M_n\to M_r$ be complex linear, positive, and trace preserving for the ordinary unnormalized trace. The trace norm is $\|A\|_1=\operatorname{tr}\sqrt{A^*A}$, and $\|T\|_{1-1}$ is the induced norm on all complex matrices. Then
--
--   $$
--   \|T\|_{1-1}=1,
--   \qquad
--   \|T(A)\|_1\le\|A\|_1\quad\text{for every }A\in M_n.
--   $$
--
--   In particular, the pointwise inequality holds for all Hermitian inputs. This is the contraction ingredient for applying the result to any independently specified family of positive trace-preserving maps; it asserts no semigroup structure or generator properties.
--
--   **Formalization Note** The pointwise inequality uses the accepted `QAlgorithms.traceNorm` definition directly, so downstream statements can use it without translating a local norm representation.
-- source:
--   Contractivity of positive and trace preserving maps under $L_p$ norms, arXiv:math-ph/0601063v1, PDF p. 3, §II, proof of II.1 and following remark

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P28

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

namespace QAlgorithms.Papers.Independent.Frontier30.P28

open QAlgorithms.Papers.Independent.Information100.P50 (M Lin schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P30 (IsPositiveMap)

open QAlgorithms.Papers.Independent.Dependency50.P26 (TracePreserving)

open QAlgorithms.Papers.Independent.Dependency50.P11 (IsUnital)

/-- The independently established trace-norm endpoint in the proof and remark,
source PDF p.3. The pointwise accepted traceNorm interface holds for every
complex matrix, hence in particular every Hermitian matrix. This assertion
contains no semigroup or generator claim. -/
theorem trace_norm_contraction
    (n r : ℕ) (hn : 0 < n) (hr : 0 < r) (T : Lin n r)
    (hpos : IsPositiveMap T) (htrace : TracePreserving T) :
    inducedPNorm 1 T = 1 ∧
    ∀ A : M n, QAlgorithms.traceNorm (T A) ≤ QAlgorithms.traceNorm A := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P28

end
