-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P40_recoveryTraceObjective
-- name    : QAlgorithms.Papers.Independent.Dependency50.P40.recoveryTraceObjective
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T15:21:46.472477+00:00
-- url     : https://prove2.me/theorems/9c505807-155f-4b46-8e8d-b27745e38236
-- title:
--   Recovery fidelity is the Choi trace objective
-- statement:
--   Let $H=\mathbb C^h$ and $K=\mathbb C^k$, $h,k>0$, and fix a density operator $\rho$ on $H$. Take any normalized finite-reference purification of $\rho$, CPTP noise $\mathcal E$ with finite Kraus family $E_j:H\to K$, and a CPTP recovery $\mathcal R:K\to H$ with Choi matrix $X_R$. Define the coefficient from the data by
--
--   $$
--   C_{\rho,\mathcal E}=\sum_j|\rho E_j^\dagger\rangle\rangle\langle\langle\rho E_j^\dagger|
--   =\sum_j(I_H\otimes E_j^*)|\rho\rangle\rangle\langle\langle\rho|(I_H\otimes E_j^T).
--   $$
--
--   Then
--
--   $$
--   F_e(\rho,\mathcal R\circ\mathcal E)
--   =\sum_j\langle\langle\rho|(I_H\otimes E_j^T)X_R(I_H\otimes E_j^*)|\rho\rangle\rangle
--   =\operatorname{tr}(X_RC_{\rho,\mathcal E}).
--   $$
--
--   Transpose and entrywise conjugation are distinct. The coefficient is constructed, not an independent parameter assumed to satisfy the identity; this is the linear objective used in (22).
-- source:
--   Optimum Quantum Error Recovery using Semidefinite Programming, arXiv:quant-ph/0606035v1, PDF p. 4, IV, Eqs. (20)-(21): recovery objective as a Choi trace inner product

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P40

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P40

open scoped ComplexConjugate ComplexOrder Matrix

open QAlgorithms.Papers.Independent.Information100.P34 (dyad)

/-- PDF p.4, (20)–(21): the recovery objective and both coefficient expressions. -/
theorem recoveryTraceObjective {h k a m : ℕ} (hh : 0 < h) (hk : 0 < k)
    (rho : Matrix (Fin h) (Fin h) ℂ) (hrho : IsDensityMatrix rho)
    (psi : EuclideanSpace ℂ (Fin a × Fin h)) (hpsi : IsPurification rho psi)
    (E : Fin m → Matrix (Fin k) (Fin h) ℂ) (hE : IsKrausFamily E)
    (R : Superop (Fin k) (Fin h)) (hR : IsChannel R) :
    recoveryCoefficient rho E =
      ∑ j, Matrix.kronecker (1 : Matrix (Fin h) (Fin h) ℂ) ((E j).map (fun z => conj z)) *
        dyad (operatorKet rho) (operatorKet rho) *
        Matrix.kronecker (1 : Matrix (Fin h) (Fin h) ℂ) (E j)ᵀ ∧
    purificationFidelity psi (R ∘ krausApply E) =
      (∑ j, complexQuadraticForm (operatorKet rho)
        (Matrix.kronecker (1 : Matrix (Fin h) (Fin h) ℂ) (E j)ᵀ * outputFirstChoi R *
          Matrix.kronecker (1 : Matrix (Fin h) (Fin h) ℂ) ((E j).map (fun z => conj z)))).re ∧
    purificationFidelity psi (R ∘ krausApply E) =
      (outputFirstChoi R * recoveryCoefficient rho E).trace.re := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P40

end
