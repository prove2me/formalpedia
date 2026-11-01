-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P47_decorrelation_converse
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P47.decorrelation_converse
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:12:09.550305+00:00
-- url     : https://prove2.me/theorems/fbbad87c-0f4b-4b76-b2cd-e321d70a82cf
-- title:
--   Proposition II.1: finite-block decorrelation converse
-- statement:
--   Let $\rho_{AB}$ be a normalized bipartite density matrix on finite nonzero spaces of dimensions $d_A,d_B$, put $d=d_Ad_B$, and let $n\ge1$. Suppose a coordinated local product-unitary ensemble $R$, with probabilities $p_i$ and $N\ge1$ terms, $\epsilon$-decorrelates $\rho^{\otimes n}$ for $\epsilon\ge0$: its output is within full trace norm $\epsilon$ of some normalized product state. Define $\eta(x)=-x\log_2x$ for $0\le x\le1/e$, with $\eta(0)=0$, and $\eta(x)=e^{-1}\log_2e$ for $x\ge1/e$. Then
--
--   $$\log_2N\ge H(p)\ge S_e(R,\rho^{\otimes n})\ge n\bigl(I(A:B)_\rho-3\epsilon\log_2d-\eta(3\epsilon)\bigr).$$
--
--   Here $e=\exp(1)$ is the natural exponential constant. The factor $n$ multiplies the entire parenthesis. This is the finite-block converse for total correlation erasure, including large error tolerances.
-- source:
--   On the quantum, classical and total amount of correlations in a quantum state, arXiv:quant-ph/0410091v2, PDF p. 3, Proposition II.1: finite-block decorrelation converse

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P47

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P47

open QAlgorithms Filter

open QAlgorithms.Papers.Independent.Gap48.P20 (Copies localProduct)

open QAlgorithms.Papers.Independent.Dependency50.P19 (mutualInformation first)

open QAlgorithms.Papers.Independent.Dependency50.P45 (entropyExchange)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon Config)

open QAlgorithms.Papers.Independent.Information100.P71 (channelPower)

open QAlgorithms.Papers.Independent.Advance50.P05 (RectangularInstrument)

open scoped Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.3, Proposition II.1: the outer n multiplies erasureEta(3 eps) as printed. -/
theorem decorrelation_converse {A B : Type} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (rho : Matrix (A × B) (A × B) ℂ)
    (hrho : IsDensityMatrix rho) (n : ℕ) (hn : 0 < n) (eps : ℝ) (heps : 0 ≤ eps)
    (R : COLUR (Copies A n) (Copies B n))
    (hR : Decorrelates (R.operation (sourcePower rho n)) eps) :
    let lower := (n : ℝ) * (mutualInformation rho - 3 * eps * logDimension A B - erasureEta (3*eps))
    lower ≤ entropyExchange R.operation (sourcePower rho n) ∧
    lower ≤ shannon R.weight ∧ lower ≤ Real.logb 2 R.count := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P47

end
