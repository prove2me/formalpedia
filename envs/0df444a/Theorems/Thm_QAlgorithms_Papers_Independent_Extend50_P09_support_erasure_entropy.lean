-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P09_support_erasure_entropy
-- name    : QAlgorithms.Papers.Independent.Extend50.P09.support_erasure_entropy
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:34:35.127633+00:00
-- url     : https://prove2.me/theorems/f5270d4f-583b-454d-8f00-cf7871611897
-- title:
--   Theorem 7: support-dependent erasure entropy bound
-- statement:
--   For finite positive-dimensional registers $P,Q$ and a positive operator $X^{PQ}$, write $H_{\min}(P|Q)_X=\sup\{h:\exists\sigma_Q\ge0,\ \operatorname{Tr}\sigma_Q=1,\ X\le2^{-h}I_P\otimes\sigma_Q\}$. The supremum is extended-real, so $H_{\min}(0)=+\infty$; throughout, $-\log_2 0=+\infty$.
--
--   Let $A$ consist of $n$ qudits of positive dimension $d$, and let $R$ consist of $k$ such qudits. Fix an actual unitary coordinate identification $A\simeq\bigoplus_j L_j\otimes R_j$ with positive dimensions $l_j,r_j$. Let $\Psi^{RA}$ be normalized and suppose its $A$ marginal is supported on the nonempty block set $J$. Let $\tau$ retain $t$ of the $n$ qudits, $0\le t\le n$, with normalized Choi state. Construct $\Xi$ as in (26)/(A5) and $\Lambda=\Xi(\Psi\otimes\operatorname{Choi}(\tau))\Xi^\dagger$. Then
--   $$H_{\min}(A^*|RE)_\Lambda\ge-(2t+k)\log_2 d-\log_2\max_{j\in J}\frac{l_j}{r_j}.$$
--
--   The block identification is unitary in both directions, and the support hypothesis concerns the input marginal. No desired norm or entropy conclusion is supplied as input.
-- source:
--   Near-optimal covariant quantum error-correcting codes from random unitaries with symmetries, arXiv:2112.01498v2, PDF p. 15, Theorem 7: support-dependent erasure entropy bound

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

/-- Theorem 7, PDF pp.15–16, (A6). Psi is normalized; the support
condition concerns its A marginal, not Lambda. The decomposition is unitary
and every included block factor has strictly positive dimension. -/
theorem support_erasure_entropy
    {J : Type} [Fintype J] [DecidableEq J]
    (d n k t : ℕ) (hd : 0 < d) (ht : t ≤ n) (l r : J → ℕ)
    (hl : ∀ j, 0 < l j) (hr : ∀ j, 0 < r j)
    (S : Matrix (SymmetryBlockCoordinates l r) (CovariantWord d n) ℂ)
    (hS : Sᴴ * S = 1) (hSrev : S * Sᴴ = 1)
    (Psi : Op (CovariantWord d k × CovariantWord d n)) (hPsi : IsDensityMatrix Psi)
    (K : Finset J) (hK : K.Nonempty)
    (hsupport : (∑ j ∈ K, blockProjector l r S j) * traceLeft Psi = traceLeft Psi) :
    ((-(2*(t : ℝ)+k)*Real.logb 2 d -
      Real.logb 2 (K.sup' hK (fun j => (l j : ℝ)/r j)) : ℝ) : EReal) ≤
        conditionalMinEntropy (generalLambda ht l r S Psi) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P09

end
