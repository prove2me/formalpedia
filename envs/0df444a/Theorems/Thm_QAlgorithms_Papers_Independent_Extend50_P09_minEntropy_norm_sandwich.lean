-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P09_minEntropy_norm_sandwich
-- name    : QAlgorithms.Papers.Independent.Extend50.P09.minEntropy_norm_sandwich
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:33:40.640172+00:00
-- url     : https://prove2.me/theorems/7bb56a04-1c52-4cea-b586-c1ff0c8896c8
-- title:
--   Lemma 3: conditional min-entropy/operator-norm sandwich
-- statement:
--   For finite positive-dimensional registers $P,Q$ and a positive operator $X^{PQ}$, write $H_{\min}(P|Q)_X=\sup\{h:\exists\sigma_Q\ge0,\ \operatorname{Tr}\sigma_Q=1,\ X\le2^{-h}I_P\otimes\sigma_Q\}$. The supremum is extended-real, so $H_{\min}(0)=+\infty$; throughout, $-\log_2 0=+\infty$.
--
--   For every positive operator $\rho^{PQ}$, with no normalization or nonzero assumption,
--   $$-\log_2\|\rho\|_\infty-\log_2\dim Q\le H_{\min}(P|Q)_\rho\le-\log_2\|\rho\|_\infty.$$
--
--   The norm is the spectral operator norm. This sandwich applies also to unnormalized operators arising from partial decoupling; the zero case has value $+\infty$.
-- source:
--   Near-optimal covariant quantum error-correcting codes from random unitaries with symmetries, arXiv:2112.01498v2, PDF p. 15, Lemma 3: conditional min-entropy/operator-norm sandwich

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P09

noncomputable section

open scoped Matrix Matrix.Norms.Elementwise ComplexConjugate ENNReal ComplexOrder

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Extend50.P09

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact generic definitions from the pinned accepted library.

open QAlgorithms.Papers.Independent.Information100.P22 (Op mixed bell)

open QAlgorithms.Papers.Independent.Information100.P67 (conditionalMinEntropy)

open QAlgorithms.Papers.Independent.Advance50.P02 (negLog)

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P09.covariantMatrixMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P09.covariantMatrixBorel

/-- Lemma 3, PDF p.15, (A1): arbitrary PSD operator including zero.
At zero both extended logarithms and conditional min-entropy are +infinity. -/
theorem minEntropy_norm_sandwich
    {A B : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (rho : Op (A × B)) (hrho : rho.PosSemidef) :
    negLog (specNorm rho) - (Real.logb 2 (Fintype.card B : ℝ) : EReal) ≤ conditionalMinEntropy rho ∧
    conditionalMinEntropy rho ≤ negLog (specNorm rho) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P09

end
