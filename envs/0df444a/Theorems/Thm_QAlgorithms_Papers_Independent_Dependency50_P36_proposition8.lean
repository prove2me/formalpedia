-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P36_proposition8
-- name    : QAlgorithms.Papers.Independent.Dependency50.P36.proposition8
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:37:37.670221+00:00
-- url     : https://prove2.me/theorems/ceb7a51b-6e6d-41d8-8673-98c6a9683ceb
-- title:
--   Pure-state second-order expansion
-- statement:
--   Let $\psi$ be a unit vector on nonzero finite-dimensional $A\otimes B$, let $\rho_A=\operatorname{Tr}_B|\psi\rangle\langle\psi|$, fix $0<\varepsilon<1$, and choose $\Omega\in\{1\text{-LOCC},\mathrm{LOCC},\mathrm{SEP},\mathrm{PPT}\}$. One-way communication is Alice to Bob; PPT maps are completely PPT-preserving. With base-two entropy $S$ and standard-normal quantile $\Phi^{-1}$,
--
--   $$E_{D,\Omega}^{(1),\varepsilon}\bigl((|\psi\rangle\langle\psi|)^{\otimes n}\bigr)=nS(\rho_A)+\sqrt{n\bigl(\operatorname{Tr}\rho_A(\log_2\rho_A)^2-S(\rho_A)^2\bigr)}\,\Phi^{-1}(\varepsilon)+O(\log n).$$
--
--   Precisely, the absolute remainder is at most $C\log_2 n$ for all integers $n\ge N$, for some $C>0,N\ge2$ depending on the fixed state, error and class. Copies have cut $A^n:B^n$; one-shot entanglement uses squared target fidelity and positive integer rank. Product states and maximally entangled states with zero dispersion remain included. This identifies a common second-order expansion across the four classes.
-- source:
--   Non-asymptotic entanglement distillation, arXiv:1706.06221v3, PDF p. 8, Proposition 8, Eq. (45): pure-state second-order expansion

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

/-- Proposition 8, arXiv:1706.06221v3, PDF pp.8–9, Eq.(45).
The unit vector constructs the pure state; n multiplies the whole variance in the radical. -/
theorem proposition8 {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (psi : EuclideanSpace ℂ (A × B)) (hpsi : ‖psi‖ = 1)
    (epsilon : ℝ) (he0 : 0 < epsilon) (he1 : epsilon < 1) (Omega : OperationClass) :
    let rhoA : Matrix A A ℂ := fun i j => ∑ b, pureDensity psi (i, b) (j, b)
    secondOrderExpansion (fun n => oneShot Omega (copies (pureDensity psi) n) epsilon)
      (vnEntropy rhoA)
      ((rhoA * (cfc log2 rhoA * cfc log2 rhoA)).trace.re - (vnEntropy rhoA) ^ 2)
      epsilon := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P36

end
