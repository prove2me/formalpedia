-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P07_logarithmic_negativity_additive
-- name    : QAlgorithms.Papers.Independent.Independent1.P07.logarithmic_negativity_additive
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:46:44.164208+00:00
-- url     : https://prove2.me/theorems/19cbc8c0-8eba-4ed0-b107-7aa6985747b2
-- title:
--   Additivity of logarithmic negativity
-- statement:
--   Let $\rho_1$ and $\rho_2$ be bipartite density matrices. Regroup their product as $(A_1A_2)|(B_1B_2)$, and define $E_N(\rho)=\log_2\|\rho^{T_A}\|_1$. Then
--
--   $$E_N(\rho_1\otimes\rho_2)=E_N(\rho_1)+E_N(\rho_2).$$
--
--   All four local spaces are finite and nonempty. This additivity concerns logarithmic negativity.
-- source:
--   A computable measure of entanglement, arXiv:quant-ph/0102117v1, §II.A, Eq. (11), PDF p. 3. https://arxiv.org/abs/quant-ph/0102117v1 . PDF SHA-256: a6bc5031b04d93cf18e71e39425eea8b9b8c938252bb87d8067d890269b90f7b.

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


















/-- Eq. (11), PDF p. 3: tensor factors are regrouped by party. -/
theorem logarithmic_negativity_additive {I J K L : Type*}
    [Fintype I] [Fintype J] [Fintype K] [Fintype L]
    [Nonempty I] [Nonempty J] [Nonempty K] [Nonempty L]
    [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq L]
    (rho : Matrix (I × J) (I × J) ℂ) (sigma : Matrix (K × L) (K × L) ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    logNeg (bipartiteTensor rho sigma) = logNeg rho+logNeg sigma := by sorry














































end QAlgorithms.Papers.Independent.Independent1.P07
