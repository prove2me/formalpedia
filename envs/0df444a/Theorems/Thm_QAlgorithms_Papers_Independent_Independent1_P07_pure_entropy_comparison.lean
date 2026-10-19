-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P07_pure_entropy_comparison
-- name    : QAlgorithms.Papers.Independent.Independent1.P07.pure_entropy_comparison
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:48:04.793979+00:00
-- url     : https://prove2.me/theorems/0739fe43-e871-4bcc-a7e7-8982d8b1e9c7
-- title:
--   Pure-state entropy comparison and equality
-- statement:
--   For normalized Schmidt data $|\psi\rangle=\sum_i c_i|u_i\rangle|v_i\rangle$, with $c_i\ge0$, write $\rho=|\psi\rangle\langle\psi|$ and $\rho_A=\operatorname{Tr}_B\rho$. Its entropy in bits satisfies
--
--   $$S(\rho_A)=2\sum_i c_i^2\log_2(1/c_i)\le2\log_2\!\left(\sum_i c_i\right)=E_N(\rho).$$
--
--   Zero coefficients contribute zero. Equality holds if and only if every pair of nonzero coefficients is equal. This includes rank-one product states and maximal entanglement on a proper Schmidt support.
-- source:
--   A computable measure of entanglement, arXiv:quant-ph/0102117v1, §V.A, Eq. (50) and equality characterization, PDF p. 7. https://arxiv.org/abs/quant-ph/0102117v1 . PDF SHA-256: a6bc5031b04d93cf18e71e39425eea8b9b8c938252bb87d8067d890269b90f7b.

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








































/-- Eq. (50) and equality characterization, PDF p. 7. Equal coefficients are
required only on the nonzero Schmidt support. -/
theorem pure_entropy_comparison {I J : Type*} [Fintype I] [Fintype J]
    [Nonempty I] [Nonempty J] [DecidableEq I] [DecidableEq J]
    {r : ℕ} (c : Fin r → ℝ) (u : Fin r → EuclideanSpace ℂ I)
    (v : Fin r → EuclideanSpace ℂ J) (hc : ∀ i, 0 ≤ c i)
    (hs : ∑ i, c i^2 = 1) (hu : Orthonormal ℂ u) (hv : Orthonormal ℂ v) :
    let rho := pureDensity (schmidtState c u v)
    let E := 2*∑ i, c i^2*Real.logb 2 ((c i)⁻¹)
    vnEntropy (traceRight rho) = E ∧ E ≤ 2*Real.logb 2 (∑ i, c i) ∧
    2*Real.logb 2 (∑ i, c i) = logNeg rho ∧
    (E = logNeg rho ↔ ∀ i j, c i ≠ 0 → c j ≠ 0 → c i = c j) := by sorry
























end QAlgorithms.Papers.Independent.Independent1.P07
