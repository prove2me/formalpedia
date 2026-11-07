-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_localExtension_support_subset
-- name    : QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.localExtension_support_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:14:08.437469+00:00
-- url     : https://prove2.me/theorems/4eba2c11-6a5c-4823-a99e-3734d0ce66ce
-- title:
--   Left Right Cayley Square Complex: local Extension support subset
-- statement:
--   The Left Right Cayley Square Complex construction uses the local Extension support subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Core.lean#L254-L271
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Core.lean#L254-L271

import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Coding_CSS_ParityChecks
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_QEC_Coding_QuantumTanner_Core
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe u v
open QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]

theorem QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.localExtension_support_subset (X : LeftRightCayleySquareComplex G A B Square)
    (vertex : G × Bool) (x : Word (ZMod 2) (A × B)) :
    hammingSupport (X.localExtension vertex x) ⊆ Finset.univ.image (X.link vertex) := by sorry
