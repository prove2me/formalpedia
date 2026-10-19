-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P07_logarithmic_negativity_not_convex
-- name    : QAlgorithms.Papers.Independent.Independent1.P07.logarithmic_negativity_not_convex
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:47:03.478002+00:00
-- url     : https://prove2.me/theorems/82166565-6fc8-4a9d-a2cd-5babab1432cb
-- title:
--   Logarithmic negativity is not convex
-- statement:
--   There exist two density matrices $\rho$ and $\sigma$ on two qubits for which
--
--   $$E_N\!\left(\frac{\rho+\sigma}{2}\right)>\frac{E_N(\rho)+E_N(\sigma)}2.$$
--
--   Thus logarithmic negativity is not convex. This states only the nonconvexity clause; the source's subsequent inference about LOCC increase is deferred separately.
-- source:
--   A computable measure of entanglement, arXiv:quant-ph/0102117v1, §II.A, unnumbered paragraph after Eq. (11), PDF p. 3. https://arxiv.org/abs/quant-ph/0102117v1 . PDF SHA-256: a6bc5031b04d93cf18e71e39425eea8b9b8c938252bb87d8067d890269b90f7b.

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



















/-- §II.A, PDF p. 3: only nonconvexity, without the erroneous LOCC-increase inference. -/
theorem logarithmic_negativity_not_convex :
    ∃ rho sigma : Matrix (Bool × Bool) (Bool × Bool) ℂ,
      IsDensityMatrix rho ∧ IsDensityMatrix sigma ∧
      (logNeg rho+logNeg sigma)/2 < logNeg ((1/2 : ℂ) • rho+(1/2 : ℂ) • sigma) := by sorry













































end QAlgorithms.Papers.Independent.Independent1.P07
