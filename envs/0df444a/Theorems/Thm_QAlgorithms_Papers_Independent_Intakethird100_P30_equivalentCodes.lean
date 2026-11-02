-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P30_equivalentCodes
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P30.equivalentCodes
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:39:07.614438+00:00
-- url     : https://prove2.me/theorems/bbf51eea-010f-4644-a728-5306a882314b
-- title:
--   II B: code equivalence preserves updated states and thresholds, (7)
-- statement:
--   Let $C$ and $D$ be nonempty codes of distinct $n$-bit words, $n\ge1$. Suppose a permutation of coordinates followed by XOR with one fixed binary word maps their underlying code sets onto one another; word enumeration is immaterial. Let $P_C(Q)$ and $P_D(Q)$ denote their Bob-only filtered six-state operators. There are local permutation unitaries $U$ on Alice and $V$ between the code-label registers, chosen independently of $Q$, such that
--
--   $$P_C(Q)=(U\otimes V)P_D(Q)(U\otimes V)^\dagger
--   \quad\text{for every }0\le Q\le\tfrac12.$$
--
--   Consequently the two operators are symmetrically extendable for exactly the same QBERs, and
--
--   $$Q_C^*=Q_D^*.$$
--
--   This is the fixed-basis interpretation of the source's equality: changing word order or coordinate labels changes matrix coefficients by local unitaries.
-- source:
--   Numerical evidence for bound secrecy from two-way post-processing in quantum key distribution, arXiv:1612.07734v2, PDF p. 4, II B: code equivalence preserves updated states and thresholds, (7)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P30

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P30

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J K L A B : Type}

variable [Fintype I] [Fintype J] [Fintype K] [Fintype L]

variable [Fintype A] [Fintype B]

/-- PDF pp.3–4, (7): equality means local permutation conjugacy, independently
of Q. Printed raw matrix equality is corrected using p.3's ordering convention. -/
theorem equivalentCodes {n : ℕ} (hn : 1 ≤ n) [Nonempty K] [Nonempty L]
    (C : K → Qubits n) (D : L → Qubits n)
    (hC : Function.Injective C) (hD : Function.Injective D)
    (hCD : CodeEquivalent C D) :
    (∃ (u : Equiv.Perm (Qubits n)) (v : L ≃ K),
      let U : Matrix (Qubits n) (Qubits n) ℂ := fun a b => if a = u b then 1 else 0
      let V : Matrix K L ℂ := fun k l => if k = v l then 1 else 0
      Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧ Vᴴ * V = 1 ∧ V * Vᴴ = 1 ∧
      ∀ Q : ℝ, 0 ≤ Q → Q ≤ 1 / 2 →
        bobState C Q = Matrix.kronecker U V * bobState D Q * (Matrix.kronecker U V)ᴴ) ∧
    (∀ Q : ℝ, 0 ≤ Q → Q ≤ 1 / 2 →
      (BobExtendible (bobState C Q) ↔ BobExtendible (bobState D Q))) ∧
    bobThreshold C = bobThreshold D := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P30

end
