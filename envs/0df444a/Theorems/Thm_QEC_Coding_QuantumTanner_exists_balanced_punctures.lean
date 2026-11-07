-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_exists_balanced_punctures
-- name    : QEC.Coding.QuantumTanner.exists_balanced_punctures
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:48:49.010211+00:00
-- url     : https://prove2.me/theorems/8ded5d62-bed5-4b89-bf05-e77f2cb53bb3
-- title:
--   Quantum Tanner: exists balanced punctures
-- statement:
--   Equal-size coordinate sets can absorb both exceptional sets without
--   increasing the larger exceptional-set size. This supplies matching punctures
--   for the resistance hypothesis, rather than assuming matching bad sets.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/TensorPuncture.lean#L136-L151
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/TensorPuncture.lean#L136-L151

import Definitions.Def_QEC_Coding_QuantumTanner_Goodness
import Definitions.Def_QEC_Coding_QuantumTanner_TensorPuncture
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe u v
variable {F : Type u} {A B : Type v} [Field F] [Fintype F] [Fintype A] [Fintype B]

theorem QEC.Coding.QuantumTanner.exists_balanced_punctures
    (badA : Finset A) (badB : Finset B) (p : Nat)
    (hCard : Fintype.card A = Fintype.card B)
    (hA : badA.card ≤ p) (hB : badB.card ≤ p) (hp : p ≤ Fintype.card A) :
    ∃ removedA : Finset A, ∃ removedB : Finset B,
      badA ⊆ removedA ∧ badB ⊆ removedB ∧
      removedA.card = removedB.card ∧ removedA.card ≤ p := by sorry
