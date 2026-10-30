-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P30_observable_mean_error
-- name    : QAlgorithms.Papers.Independent.Advance50.P30.observable_mean_error
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:54:54.12567+00:00
-- url     : https://prove2.me/theorems/10ce0794-255e-4f92-b182-a79bcbe0152e
-- title:
--   Lemma 4: distribution error controls observable-mean error
-- statement:
--   Let $\mathcal H$ have finite dimension $d\ge1$, and let $L=\sum_{i=1}^t s_iL_i$, where $t\ge1$, all $s_i\in\mathbb R$, and the $L_i$ are Hermitian with $\operatorname{Tr}(L_iL_j^\dagger)=\delta_{ij}$. Let $\rho$ be a normalized density operator. For each $i$, write $L_i=\sum_a\lambda_{ia}\Pi_{ia}$ for its spectral decomposition, set $P_{ia}=\operatorname{Tr}(\Pi_{ia}\rho)$, and let $Q_i$ be any normalized probability distribution on the same spectral alphabet. Then
--   $$
--   \left|\operatorname{Tr}(L\rho)-\sum_i s_i\sum_a\lambda_{ia}Q_{ia}\right|
--   \le\sqrt t\,\|L\|_{\mathrm{HS}}\max_i\sum_a|P_{ia}-Q_{ia}|.
--   $$
--
--   The Hilbert–Schmidt norm is $\|L\|_{\mathrm{HS}}=\sqrt{\operatorname{Tr}(L^\dagger L)}$. This estimate converts distribution-frequency control into mean-value control, including negative coefficients. The maximum is over a nonempty finite set.
-- source:
--   Unconditional privacy over channels which cannot convey quantum information, arXiv:quant-ph/0702077v1, PDF p. 17, Lemma 4

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P30

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P30

open QAlgorithms MeasureTheory

open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)

open QAlgorithms.Papers.Independent.Information100.P21 (Op Vec)

open QAlgorithms.Papers.Independent.Information100.P69 (permute)

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

attribute [local instance] Classical.decEq Classical.propDecidable

attribute [local instance] QAlgorithms.Papers.Independent.Advance50.P30.matrixContinuousENorm

attribute [local instance] QAlgorithms.Papers.Independent.Advance50.P30.matrixMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Advance50.P30.matrixBorel

attribute [local instance] QAlgorithms.Papers.Independent.Advance50.P30.vectorMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Advance50.P30.vectorBorel

/-- PDF p.17, Lemma 4, Eq.(15), with arbitrary signed real coefficients.
The proof's operator-norm equality is unnecessary; HS normalization gives
operator norm at most one. The nonempty finite sSup is the actual maximum. -/
theorem observable_mean_error {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (t : ℕ) (ht : 0 < t) (D : HSDecomposition I t)
    (rho : Op I) (hrho : IsDensityMatrix rho)
    (Q : (i : Fin t) → Fin (D.intermediate i).count → ℝ)
    (hQpos : ∀ i a, 0 ≤ Q i a) (hQsum : ∀ i, ∑ a, Q i a = 1) :
    |(D.operator * rho).trace.re -
      ∑ i, D.coeff i * ∑ a, (D.intermediate i).value a * Q i a| ≤
      Real.sqrt t * frobNorm D.operator *
        sSup (Set.range fun i : Fin t =>
          l1 (fun a => effectProb ((D.intermediate i).effect a) rho) (Q i)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P30

end
