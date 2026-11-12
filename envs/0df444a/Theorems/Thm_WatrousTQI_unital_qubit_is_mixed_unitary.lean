-- Prove2me | Theorems.Thm_WatrousTQI_unital_qubit_is_mixed_unitary
-- name    : WatrousTQI.unital_qubit_is_mixed_unitary
-- status  : Open
-- author  : @Mrnaiq
-- created : 2026-11-11T22:58:27.330501+00:00
-- url     : https://prove2.me/theorems/9bb7db0a-0b39-473c-92bd-755bb0a95ddf
-- title:
--   Theorem 4.23 — unital qubit channels are mixed unitary
-- statement:
--   Every trace-preserving completely positive map $\Phi$ on a two-dimensional complex quantum system that preserves the identity admits a finite random-unitary representation. There are a finite number $k$, real probabilities $p_0,\ldots,p_{k-1}$ in $[0,1]$ summing to one, and unitary matrices $U_0,\ldots,U_{k-1}$ such that $$\Phi(X)=\sum_{j=0}^{k-1}p_jU_jXU_j^\dagger$$ for every complex $2\times2$ matrix $X$. The same probabilities and unitaries work for every operator. The statement fixes no number of terms and includes boundary cases with zero probabilities. It reuses the published random-unitary predicate instead of introducing a competing definition.
-- source:
--   John Watrous, The Theory of Quantum Information, Cambridge University Press, 2018, Chapter 4. https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf; Theorem 4.23, printed p.226 (PDF p.234), with Definition 4.2, printed p.202 (PDF p.210).

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P11
set_option autoImplicit false
noncomputable section
open scoped Matrix ComplexConjugate BigOperators

namespace WatrousTQI

theorem unital_qubit_is_mixed_unitary
    (Φ : QAlgorithms.Superop (Fin 2) (Fin 2))
    (hΦ : QAlgorithms.IsChannel Φ)
    (hu : Φ (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1) :
    QAlgorithms.Papers.Independent.Dependency50.P11.IsRandomUnitary Φ := by sorry

end WatrousTQI
