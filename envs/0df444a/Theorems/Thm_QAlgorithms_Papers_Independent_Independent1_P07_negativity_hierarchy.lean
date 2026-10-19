-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P07_negativity_hierarchy
-- name    : QAlgorithms.Papers.Independent.Independent1.P07.negativity_hierarchy
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:46:58.891087+00:00
-- url     : https://prove2.me/theorems/84c1dc64-bf5c-4ebf-b47b-a2ca8a684cfb
-- title:
--   Hierarchy and vanishing sets
-- statement:
--   For a density matrix $\rho$ on positive finite local spaces, let $N_{ss}$ and $N_{ppts}$ use the variational base construction with separable states and PPT states, respectively. Then
--
--   $$N_{ss}(\rho)\ge N_{ppts}(\rho)\ge N(\rho)\ge0.$$
--
--   Furthermore, $N_{ss}(\rho)=0$ exactly when $\rho$ is separable; $N_{ppts}(\rho)=0$ and $N(\rho)=0$ each hold exactly when $\rho^{T_A}\ge0$. These zero sets distinguish the measures. The phrase “in general” is not a universal strictness condition.
-- source:
--   A computable measure of entanglement, arXiv:quant-ph/0102117v1, §II.C, Eq. (21), PDF p. 4. https://arxiv.org/abs/quant-ph/0102117v1 . PDF SHA-256: a6bc5031b04d93cf18e71e39425eea8b9b8c938252bb87d8067d890269b90f7b.

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





















/-- Eq. (21) and vanishing sets, PDF p. 4. Strictness is not claimed on every state. -/
theorem negativity_hierarchy {I J : Type*} [Fintype I] [Fintype J]
    [Nonempty I] [Nonempty J] [DecidableEq I] [DecidableEq J]
    (rho : Matrix (I × J) (I × J) ℂ) (hrho : IsDensityMatrix rho) :
    0 ≤ negativity rho ∧ negativity rho ≤ pptRobustness rho ∧
    pptRobustness rho ≤ separableRobustness rho ∧
    (separableRobustness rho = 0 ↔ IsSeparableDensity rho) ∧
    (pptRobustness rho = 0 ↔ (partialTransposeFirst rho).PosSemidef) ∧
    (negativity rho = 0 ↔ (partialTransposeFirst rho).PosSemidef) := by sorry











































end QAlgorithms.Papers.Independent.Independent1.P07
