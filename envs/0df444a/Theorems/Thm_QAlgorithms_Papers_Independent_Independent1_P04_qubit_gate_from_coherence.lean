-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P04_qubit_gate_from_coherence
-- name    : QAlgorithms.Papers.Independent.Independent1.P04.qubit_gate_from_coherence
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:23:31.117046+00:00
-- url     : https://prove2.me/theorems/59053bd3-357a-475f-b0f6-5b81ef1804ae
-- title:
--   A coherent qubit implements any qubit unitary
-- statement:
--   Let $U$ be a unitary on a qubit. For $b\in\{0,1\}$ define
--   $$K_b=\sum_{i,j=0}^1 U_{ij}|i,b\rangle\langle j,i\mathbin{\oplus}b|.$$
--   These matrices are chosen from $U$ before the unknown input. They preserve diagonal positive matrices, obey $\sum_bK_b^\dagger K_b=I$, and for every unit input $|\phi\rangle$,
--   $$K_b(|\phi\rangle\otimes|+\rangle)=2^{-1/2}(U|\phi\rangle)\otimes|b\rangle.$$
--   Both outcomes implement the desired gate, consuming one coherent resource qubit.
-- source:
--   Quantifying Coherence, arXiv:1311.0275v3, Appendix B (B.1)–(B.4), PDF p. 6. https://arxiv.org/abs/1311.0275v3 . PDF SHA-256: c70b296ff2628a49bfb6ffd3e0abb02ad1aa50162dec040cf32047eb3a450825.

import Definitions.Def_QAlgorithms_Defs_BasisCoherence
import Definitions.Def_QAlgorithms_Defs_ExtendedQuantumEntropy
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P04_Model
set_option autoImplicit false

/-! Quantifying Coherence, arXiv:1311.0275v3. Fixed bases and arbitrary finite dimensions.
Local predicates apply to density matrices only; invalid matrices carry no coherence guarantees. -/

noncomputable section

open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Independent1.P04

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

















































/-- PDF p.6, (B.1)–(B.4): two fixed branches implement U on every normalized input qubit. -/
theorem qubit_gate_from_coherence (U : Matrix.unitaryGroup Bool ℂ) :
    IsKrausFamily (qubitResourceKraus U) ∧
    (∀ b, PreservesDiagonalBranch (qubitResourceKraus U b)) ∧
    ∀ phi : EuclideanSpace ℂ Bool, IsState phi → ∀ b : Bool,
      act (qubitResourceKraus U b) (tensorVec phi (act hadamard (ket false))) =
        ((Real.sqrt 2)⁻¹ : ℂ) • tensorVec (act U phi) (ket b) := by sorry

















end QAlgorithms.Papers.Independent.Independent1.P04
