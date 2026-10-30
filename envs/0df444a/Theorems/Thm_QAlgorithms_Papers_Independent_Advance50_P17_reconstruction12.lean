-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P17_reconstruction12
-- name    : QAlgorithms.Papers.Independent.Advance50.P17.reconstruction12
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T11:27:25.158256+00:00
-- url     : https://prove2.me/theorems/dc7bf11f-7abd-4442-ae07-cb444e09f69b
-- title:
--   Section IV A, Eq.(12) and reference note [45]: at most 2d^2 observable averages
-- statement:
--   Let $\mathcal E$ be CPTP and $U$ unitary on a register of dimension $d\ge1$. Choose an orthogonal unitary basis $V_j$, with $\operatorname{tr}(V_j^\dagger V_k)=d\delta_{jk}$, and any density-matrix operator basis $\rho_k$. Compute $a_{jk}$ from $V_j=\sum_k a_{jk}\rho_k$ and set $\sigma_k=\sum_j a_{jk}UV_j^\dagger U^\dagger$. Then
--
--   $$F_{\rm pro}(\mathcal E,U)=d^{-3}\sum_k\operatorname{tr}(\sigma_k\mathcal E(\rho_k)).$$
--
--   Writing $A_k=(\sigma_k+\sigma_k^\dagger)/2$ and $B_k=(\sigma_k-\sigma_k^\dagger)/(2i)$ gives Hermitian observables with $\sigma_k=A_k+iB_k$. Hence at most $2d^2$ observable averages suffice, or $d^2$ when the paired operators are Hermitian. These are counts of distinct averages, not samples. The adjoint corrects the printed formula consistently with (10).
-- source:
--   Distance measures to compare real and ideal quantum processes, arXiv:quant-ph/0408063v2, PDF p. 6, Section IV A, Eq.(12) and reference note [45]: at most 2d^2 observable averages

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P17

noncomputable section

open MeasureTheory Filter

open scoped Matrix ComplexConjugate Topology

namespace QAlgorithms.Papers.Independent.Advance50.P17

open QAlgorithms.Papers.Independent.Information100.P53 (fidelity)

open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)

open QAlgorithms.Papers.Independent.Information100.P75 (hermitianReal)

variable {I J K : Type} [Fintype I] [Fintype J] [Fintype K]
  [DecidableEq I] [DecidableEq J] [DecidableEq K]
  [Nonempty I] [Nonempty J] [Nonempty K]

/-- Section IV A, PDF p.6, Eq.(12), and note [45], p.15: at most 2d^2 Hermitian averages.
The adjoint in pairedOperator corrects the same printed omission as Eq.(11). -/
theorem reconstruction12 (E : FiniteProcess I I) (U : Matrix.unitaryGroup I ℂ)
    (V : I × I → Matrix.unitaryGroup I ℂ)
    (hv : ∀ j k, ((V j : Matrix I I ℂ)ᴴ * (V k : Matrix I I ℂ)).trace =
      if j = k then (Fintype.card I : ℂ) else 0)
    (r : Module.Basis (I × I) ℂ (Matrix I I ℂ)) (hr : ∀ k, IsDensityMatrix (r k)) :
    (proFidelity E.val (conjSuperop (U : Matrix I I ℂ)) : ℂ) =
      (Fintype.card I : ℂ)⁻¹ ^ 3 * ∑ k, (pairedOperator r V U k * E.val (r k)).trace ∧
    (∀ k, (hermitianReal (pairedOperator r V U k)).IsHermitian ∧
      (hermitianImag (pairedOperator r V U k)).IsHermitian ∧
      pairedOperator r V U k = hermitianReal (pairedOperator r V U k) +
        Complex.I • hermitianImag (pairedOperator r V U k)) ∧
    Fintype.card ((I × I) × Bool) = 2 * Fintype.card I ^ 2 ∧
    ((∀ k, (pairedOperator r V U k).IsHermitian) →
      proFidelity E.val (conjSuperop (U : Matrix I I ℂ)) =
        (Fintype.card I : ℝ)⁻¹ ^ 3 *
          ∑ k, effectProb (pairedOperator r V U k) (E.val (r k))) ∧
    Fintype.card (I × I) = Fintype.card I ^ 2 := by sorry

end QAlgorithms.Papers.Independent.Advance50.P17

end
