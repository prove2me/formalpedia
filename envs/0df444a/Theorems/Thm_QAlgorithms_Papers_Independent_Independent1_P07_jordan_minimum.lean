-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P07_jordan_minimum
-- name    : QAlgorithms.Papers.Independent.Independent1.P07.jordan_minimum
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:46:49.037253+00:00
-- url     : https://prove2.me/theorems/32a214be-d8f4-4ef9-b7ea-065fa222bd8c
-- title:
--   Attained Jordan variational decomposition
-- statement:
--   Let $A$ be a Hermitian matrix on a positive finite-dimensional space. There exist density matrices $\rho_+,\rho_-$ and $a_+,a_-\ge0$ such that
--
--   $$A=a_+\rho_+-a_-\rho_-,\qquad \|A\|_1=a_++a_-,\qquad a_-=\sum_k\max\{0,-\lambda_k(A)\}.$$
--
--   Their coefficient sum is no larger than that of any other such decomposition. Eigenvalues are counted with multiplicity. This is an attained variational characterization, valid also for $A=0$.
-- source:
--   A computable measure of entanglement, arXiv:quant-ph/0102117v1, §II.A, Lemma 2, Eq. (8), PDF p. 3. https://arxiv.org/abs/quant-ph/0102117v1 . PDF SHA-256: a6bc5031b04d93cf18e71e39425eea8b9b8c938252bb87d8067d890269b90f7b.

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

















/-- Lemma 2 and Eq. (8), PDF p. 3: attained minimum and negative spectral mass. -/
theorem jordan_minimum {I : Type*} [Fintype I] [Nonempty I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A.IsHermitian) :
    ∃ ap am : ℝ, ∃ rp rm : Matrix I I ℂ,
      JordanDecomposition A ap am rp rm ∧ traceNorm A = ap+am ∧ am = negativeMass A ∧
      ∀ bp bm sp sm, JordanDecomposition A bp bm sp sm → ap+am ≤ bp+bm := by sorry















































end QAlgorithms.Papers.Independent.Independent1.P07
