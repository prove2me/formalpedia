-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P28_hermitian_traceless_sharp_bound
-- name    : QAlgorithms.Papers.Independent.Frontier30.P28.hermitian_traceless_sharp_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T17:18:55.530083+00:00
-- url     : https://prove2.me/theorems/9d883a8f-2c49-4430-8e9f-99c78cda6415
-- title:
--   Optimal Schatten bound on traceless Hermitian matrices
-- statement:
--   Let $n\ge2$, and let $H_0=\{A\in M_n:A=A^*,\ \operatorname{tr}A=0\}$. All traces are ordinary unnormalized traces. For $1\le p\le\infty$, define $\|T|_{H_0}\|_{p-p}$ as the supremum of $\|T(A)\|_p$ over $A\in H_0$ with $\|A\|_p\le1$. Every positive trace-preserving complex-linear map $T:M_n\to M_n$ obeys
--
--   $$
--   \|T|_{H_0}\|_{p-p}\le B_{n,p},\qquad
--   B_{n,p}=\begin{cases}
--   (n/2)^{1-1/p},&p<\infty,\ n\text{ even},\\
--   \left(\dfrac{2^{2-p}}{(n-1)^{1-p}+(n+1)^{1-p}}\right)^{1/p},&p<\infty,\ n\text{ odd},\\
--   \lfloor n/2\rfloor,&p=\infty.
--   \end{cases}
--   $$
--
--   There exists a completely positive trace-preserving map, chosen for $n$ independently of $p$, for which equality holds for every $1\le p\le\infty$.
--
--   This is the optimal uniform bound for distances between density matrices on the traceless Hermitian subspace. The infinity value is the limit of the finite-exponent expression. The domain $n\ge2$ retains the nonzero traceless subspace and the source's two-output-state sharpness construction.
-- source:
--   Contractivity of positive and trace preserving maps under $L_p$ norms, arXiv:math-ph/0601063v1, PDF p. 4, Theorem III.1, with sharpness on PDF p.5

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P28

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

namespace QAlgorithms.Papers.Independent.Frontier30.P28

open QAlgorithms.Papers.Independent.Information100.P50 (M Lin schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P30 (IsPositiveMap)

open QAlgorithms.Papers.Independent.Dependency50.P26 (TracePreserving)

open QAlgorithms.Papers.Independent.Dependency50.P11 (IsUnital)

/-- Theorem III.1, source PDF pp.4–5: optimal induced norm on H_0.
The sharpness construction uses two distinct output basis states, hence n ≥ 2.
One CPTP witness can be chosen before p, as in the source's rank-ceil(n/2)
projector construction. At infinity the displayed formula means its limit. -/
theorem hermitian_traceless_sharp_bound
    (n : ℕ) (hn : 2 ≤ n) :
    (∀ (p : ℝ≥0∞), 1 ≤ p → ∀ T : Lin n n,
      IsPositiveMap T → TracePreserving T →
      restrictedPNorm p T InHermitianTraceZero ≤
        ENNReal.ofReal (hermitianTraceZeroBound n p)) ∧
    (∃ T : Lin n n,
      QAlgorithms.Entanglement.IsCompletelyPositive T ∧ TracePreserving T ∧
      ∀ p : ℝ≥0∞, 1 ≤ p →
        restrictedPNorm p T InHermitianTraceZero =
          ENNReal.ofReal (hermitianTraceZeroBound n p)) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P28

end
