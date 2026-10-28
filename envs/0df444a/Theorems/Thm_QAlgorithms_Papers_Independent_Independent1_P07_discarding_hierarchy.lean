-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P07_discarding_hierarchy
-- name    : QAlgorithms.Papers.Independent.Independent1.P07.discarding_hierarchy
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:48:28.483184+00:00
-- url     : https://prove2.me/theorems/731b0fe2-91b8-4087-b47a-790402eba712
-- title:
--   Hierarchy under discarding
-- statement:
--   For a four-party density matrix $\rho_{ABCD}$, form $\rho_{ABC}=\operatorname{Tr}_D\rho$ and $\rho_{AB}=\operatorname{Tr}_C\rho_{ABC}$. Then
--
--   $$N_{A|BCD}(\rho)\ge N_{A|BC}(\rho_{ABC})\ge N_{A|B}(\rho_{AB}),$$
--
--   and the same two inequalities hold for $E_N$. These compare the measures and hence their distillation upper bounds. They do not compare actual optimal rates of different distillation tasks.
-- source:
--   A computable measure of entanglement, arXiv:quant-ph/0102117v1, §VI.B, Eq. (66), PDF p. 10. https://arxiv.org/abs/quant-ph/0102117v1 . PDF SHA-256: a6bc5031b04d93cf18e71e39425eea8b9b8c938252bb87d8067d890269b90f7b.

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



















































/-- Eq. (66), PDF p. 10, both measures and both successive partial traces. -/
theorem discarding_hierarchy {A B C D : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]
    (rho : Matrix (A × ((B × C) × D)) (A × ((B × C) × D)) ℂ)
    (hrho : IsDensityMatrix rho) :
    let rABC := traceRight (rho.submatrix (fun z : (A × (B × C)) × D => (z.1.1,(z.1.2,z.2)))
      (fun z : (A × (B × C)) × D => (z.1.1,(z.1.2,z.2))))
    let rAB := traceRight (rABC.submatrix (fun z : (A × B) × C => (z.1.1,(z.1.2,z.2)))
      (fun z : (A × B) × C => (z.1.1,(z.1.2,z.2))))
    negativity rAB ≤ negativity rABC ∧ negativity rABC ≤ negativity rho ∧
    logNeg rAB ≤ logNeg rABC ∧ logNeg rABC ≤ logNeg rho := by sorry













end QAlgorithms.Papers.Independent.Independent1.P07
