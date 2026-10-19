-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P07_base_properties
-- name    : QAlgorithms.Papers.Independent.Independent1.P07.base_properties
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:46:59.159765+00:00
-- url     : https://prove2.me/theorems/bd90b816-f305-4cd1-8740-cbc65ed2841c
-- title:
--   Base norm and generalized negativity
-- statement:
--   Let $S$ be a compact convex set of Hermitian trace-one matrices whose real span is the full Hermitian space. Define $\|A\|_S$ and $N_S(A)$ as the infima of $a_++a_-$ and $a_-$ over $A=a_+\rho_+-a_-\rho_-$, where $a_\pm\ge0$ and $\rho_\pm\in S$. These sets are nonempty and bounded below. The first functional is a norm on Hermitian matrices; $N_S$ is convex and nonnegative. Moreover,
--
--   $$\operatorname{Tr}A=1\ \Longrightarrow\ \|A\|_S=1+2N_S(A).$$
--
--   Members of $S$ need not be positive. The statement includes definiteness, the triangle inequality, and absolute homogeneity of the norm.
-- source:
--   A computable measure of entanglement, arXiv:quant-ph/0102117v1, §II.C, Eqs. (18)–(20), PDF p. 4. https://arxiv.org/abs/quant-ph/0102117v1 . PDF SHA-256: a6bc5031b04d93cf18e71e39425eea8b9b8c938252bb87d8067d890269b90f7b.

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




















/-- Eqs. (18)–(20), PDF p. 4: well-defined infima, all norm axioms on Hermitian
matrices, convex nonnegative generalized negativity, and the trace-one identity. -/
theorem base_properties {I : Type*} [Fintype I] [Nonempty I] [DecidableEq I]
    (S : Set (Matrix I I ℂ)) (hS : IsBase S) :
    (∀ A : Matrix I I ℂ, A.IsHermitian →
      (∃ ap am rp rm, BaseDecomposition S A ap am rp rm) ∧
      BddBelow {v | ∃ ap am rp rm, BaseDecomposition S A ap am rp rm ∧ v = ap+am} ∧
      BddBelow {v | ∃ ap am rp rm, BaseDecomposition S A ap am rp rm ∧ v = am} ∧
      0 ≤ baseNorm S A ∧ (baseNorm S A = 0 ↔ A = 0) ∧ 0 ≤ baseNeg S A ∧
      (A.trace = 1 → baseNorm S A = 1+2*baseNeg S A)) ∧
    (∀ (A B : Matrix I I ℂ), A.IsHermitian → B.IsHermitian →
      baseNorm S (A+B) ≤ baseNorm S A+baseNorm S B) ∧
    (∀ (A : Matrix I I ℂ) (t : ℝ), A.IsHermitian →
      baseNorm S ((t : ℂ) • A) = |t| * baseNorm S A) ∧
    (∀ (q : ℕ) (p : Fin q → ℝ) (A : Fin q → Matrix I I ℂ),
      (∀ i, 0 ≤ p i) → (∑ i, p i = 1) → (∀ i, (A i).IsHermitian) →
      baseNeg S (∑ i, (p i : ℂ) • A i) ≤ ∑ i, p i*baseNeg S (A i)) := by sorry












































end QAlgorithms.Papers.Independent.Independent1.P07
