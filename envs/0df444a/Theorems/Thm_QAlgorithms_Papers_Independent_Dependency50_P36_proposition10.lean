-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P36_proposition10
-- name    : QAlgorithms.Papers.Independent.Dependency50.P36.proposition10
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:39:12.346369+00:00
-- url     : https://prove2.me/theorems/481a1b14-02dd-442a-939c-3c8432b28c7c
-- title:
--   Finite maximally correlated expansion
-- statement:
--   Let $d\ge1$ and let $\widetilde\rho$ be a positive semidefinite trace-one $d\times d$ matrix in fixed bases. Construct $\rho_{\mathrm{mc}}=\sum_{i,j}\widetilde\rho_{ij}|ii\rangle\langle jj|$, and let $\Delta$ dephase the full product basis. Fix $0<\varepsilon<1$ and $\Omega\in\{1\text{-LOCC},\mathrm{LOCC},\mathrm{SEP},\mathrm{PPT}\}$, with Alice-to-Bob one-way communication and completely PPT-preserving PPT maps. Then
--
--   $$E_{D,\Omega}^{(1),\varepsilon}(\rho_{\mathrm{mc}}^{\otimes n})=nD(\rho_{\mathrm{mc}}\|\Delta\rho_{\mathrm{mc}})+\sqrt{nV(\rho_{\mathrm{mc}}\|\Delta\rho_{\mathrm{mc}})}\,\Phi^{-1}(\varepsilon)+O(\log n).$$
--
--   Relative entropy is in bits, $V$ is the variance of the log-likelihood difference under its first argument, and $\Phi$ is the standard normal CDF. The absolute remainder is at most $C\log_2n$ for all integers $n\ge N$, for some $C>0,N\ge2$ depending on the fixed data. The one-shot quantity uses integer target rank and squared fidelity on the grouped $A^n:B^n$ cut. This is a finite-dimensional statement, including $d=1$ and zero dispersion.
-- source:
--   Non-asymptotic entanglement distillation, arXiv:1706.06221v3, PDF p. 10, Proposition 10, Eq. (51): finite maximally correlated states

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P36

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Dependency50.P36

open QAlgorithms.Papers.Independent.Information100.P03 (partialTransposeB)

open QAlgorithms.Papers.Independent.Information100.P04 (copies)

open QAlgorithms.Papers.Independent.Information100.P21 (FiniteLOCC)

open QAlgorithms.Papers.Independent.Information100.P34 (dephasing)

open QAlgorithms.Papers.Independent.Information100.P63 (testingBeta normalCDF normalQuantile)

open QAlgorithms.Papers.Independent.Information100.P80 (log2)

/-- Proposition 10, arXiv:1706.06221v3, PDF pp.9–10, Eqs.(50)–(51).
Construct the state and its dephased comparator from a finite density matrix. -/
theorem proposition10 {d : ℕ} (hd : 0 < d)
    (rhoTilde : Matrix (Fin d) (Fin d) ℂ) (hrho : IsDensityMatrix rhoTilde)
    (epsilon : ℝ) (he0 : 0 < epsilon) (he1 : epsilon < 1) (Omega : OperationClass) :
    let rho := maximallyCorrelated rhoTilde
    secondOrderExpansion (fun n => oneShot Omega (copies rho n) epsilon)
      (relativeEntropyFinite rho (dephasing rho))
      (pairInformationVariance rho (dephasing rho)) epsilon := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P36

end
