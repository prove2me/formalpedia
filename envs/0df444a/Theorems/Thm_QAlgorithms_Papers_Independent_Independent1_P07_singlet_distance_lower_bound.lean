-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P07_singlet_distance_lower_bound
-- name    : QAlgorithms.Papers.Independent.Independent1.P07.singlet_distance_lower_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:47:51.368749+00:00
-- url     : https://prove2.me/theorems/2bb708f7-6390-478a-b071-48a383225fa7
-- title:
--   Singlet-distance lower bound
-- statement:
--   Let $m\ge1$ and let $\rho$ be a state on $\mathbb C^m\otimes\mathbb C^m$. Let $P_+$ be its standard maximally entangled state, and let $\Delta(P_+,\rho)$ be the infimum of $\|P_+-P(\rho)\|_1$ over deterministic LOCC protocols $P$. Then
--
--   $$\Delta(P_+,\rho)\ge2\left(1-\frac{1+2N(\rho)}m\right).$$
--
--   The trace norm is unhalved. No optimal protocol is assumed to exist.
-- source:
--   A computable measure of entanglement, arXiv:quant-ph/0102117v1, §III.A, Proposition 4, Eq. (30), PDF p. 5. https://arxiv.org/abs/quant-ph/0102117v1 . PDF SHA-256: a6bc5031b04d93cf18e71e39425eea8b9b8c938252bb87d8067d890269b90f7b.

import Definitions.Def_QAlgorithms_Defs_EntanglementNegativity
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Defs_QuditChannelFidelities
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P07_Model
set_option autoImplicit false

/-! Vidal–Werner, arXiv:quant-ph/0102117v1. All locators are PDF pages.
Paper-local operational and variational definitions precede their statements.
Deferred source inconsistencies and interfaces are recorded in HARD.md. -/

noncomputable section

open scoped Matrix ComplexOrder NNReal ENNReal

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Independent1.P07

open Entanglement




































/-- Proposition 4, Eq. (30), PDF pp. 4–5, using the unhalved distance. -/
theorem singlet_distance_lower_bound {m : ℕ} (hm : 0 < m)
    (rho : Matrix (Fin m × Fin m) (Fin m × Fin m) ℂ) (hrho : IsDensityMatrix rho) :
    2*(1-(1+2*negativity rho)/(m : ℝ)) ≤ singletDistance m hm rho := by sorry




























end QAlgorithms.Papers.Independent.Independent1.P07
