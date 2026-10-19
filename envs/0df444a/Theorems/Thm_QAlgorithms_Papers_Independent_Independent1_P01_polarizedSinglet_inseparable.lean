-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P01_polarizedSinglet_inseparable
-- name    : QAlgorithms.Papers.Independent.Independent1.P01.polarizedSinglet_inseparable
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:05:48.314165+00:00
-- url     : https://prove2.me/theorems/c8a051fb-73f6-4f22-a9d7-fa9d5116b16a
-- title:
--   Every positive singlet fraction in the polarized mixture is inseparable
-- statement:
--   Let $S$ be the two-qubit singlet density matrix and let $0<x\le1$. Define $\rho_x=xS+(1-x)|00\rangle\langle00|$ and $\sigma_x=\rho_x^{T_I}$. Then
--
--   $$\lambda_{\min}(\sigma_x)<0,\qquad \rho_x\ \text{is inseparable}.$$
--
--   Thus even an arbitrarily small positive singlet fraction in this family produces entanglement. The zero-fraction endpoint is excluded by the source's positivity condition.
-- source:
--   Separability Criterion for Density Matrices, arXiv:quant-ph/9604005v2, Eq. (15) and following paragraph, PDF p. 4. https://arxiv.org/abs/quant-ph/9604005v2 . PDF SHA-256: 6574d1af38e331a5ed4f7c58673855e1e580eb96d79fa52338f18cdc22d43998.

import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
import Definitions.Def_QAlgorithms_Defs_Hamiltonian
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P01_Model
set_option autoImplicit false

/-!
# Peres: Separability Criterion for Density Matrices

Source: arXiv:quant-ph/9604005v2, PDF pp.2–5. The first subsystem alone
is transposed, without complex conjugation. Equation (5), which has a
conjugating-factor defect, is deferred; its valid spectral conclusion is stated.
-/

noncomputable section

open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Independent1.P01

open QAlgorithms.Entanglement

















/-- Peres PDF p.4, Eq. (15) and the following paragraph: every positive singlet
fraction gives a negative partial-transpose eigenvalue and an inseparable state. -/
theorem polarizedSinglet_inseparable (x : ℝ) (positive : 0 < x) (fraction : x ≤ 1) :
    (∃ k, ascEigenvalues (partialTransposeFirst (polarizedSingletDensity x)) k < 0) ∧
      ¬ IsSeparableDensity (polarizedSingletDensity x) := by sorry


end QAlgorithms.Papers.Independent.Independent1.P01
