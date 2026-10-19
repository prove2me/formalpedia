-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P07_distillation_rate_bound
-- name    : QAlgorithms.Papers.Independent.Independent1.P07.distillation_rate_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:47:40.298269+00:00
-- url     : https://prove2.me/theorems/fa058ae7-50c6-45af-81ed-57728bf1abcf
-- title:
--   Distillation-rate upper bound
-- statement:
--   Let $\rho$ be a finite bipartite density matrix and $0\le\varepsilon<1$. Define achievable nonnegative rates using the source's universal condition on diverging integer sequences: $m_\alpha$ counts input copies, $n_\alpha$ output Bell pairs, and $\limsup n_\alpha/m_\alpha\le c$ requires $\limsup\Delta(\Upsilon^{\otimes n_\alpha},\rho^{\otimes m_\alpha})\le\varepsilon$. The supremum $E_D^\varepsilon$ is taken in the extended nonnegative reals. Then
--
--   $$E_D^\varepsilon(\rho)\le E_N(\rho).$$
--
--   The case $\varepsilon=0$ is included. The input/output letter interchange near Eq. (41) is resolved by Eq. (43) and the proof.
-- source:
--   A computable measure of entanglement, arXiv:quant-ph/0102117v1, §IV, Proposition 7, Eq. (44), PDF p. 7. https://arxiv.org/abs/quant-ph/0102117v1 . PDF SHA-256: a6bc5031b04d93cf18e71e39425eea8b9b8c938252bb87d8067d890269b90f7b.

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



























































/-- Proposition 7, Eq. (44), PDF pp. 6–7, including eps = 0 and excluding eps = 1. -/
theorem distillation_rate_bound {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (rho : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hrho : IsDensityMatrix rho)
    (eps : ℝ) (heps : 0 ≤ eps) (hepsOne : eps < 1) :
    distillableEntanglement rho eps ≤ ENNReal.ofReal (logNeg rho) := by sorry





end QAlgorithms.Papers.Independent.Independent1.P07
