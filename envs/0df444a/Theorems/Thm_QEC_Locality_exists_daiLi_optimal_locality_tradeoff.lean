-- Prove2me | Theorems.Thm_QEC_Locality_exists_daiLi_optimal_locality_tradeoff
-- name    : QEC.Locality.exists_daiLi_optimal_locality_tradeoff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T05:42:39.685641+00:00
-- url     : https://prove2.me/theorems/90977aef-5069-422d-b3be-7a12e5548ff6
-- title:
--   Locality: exists dai Li optimal locality tradeoff
-- statement:
--   Dai--Li's optimal locality tradeoff [DL24, Theorem 1.2] for a finite binary
--   stabilizer code with one fixed independent Pauli-generator presentation.
--
--   The outer existential witnesses are absolute across every presentation and
--   unit-separated embedding.  The conclusion counts the cardinality of the
--   actual finite set of distinct unordered generator interactions; it makes no
--   comparison between different generator presentations.  The selected witnesses
--   are Lean-QEC proof constants, not constants attributed to DL24.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Results/LocalityBounds/OptimalTradeoff.lean#L90-L123
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Results/LocalityBounds/OptimalTradeoff.lean#L90-L123

import Definitions.Def_QEC_Locality_OptimalTradeoff_FinalComposition
import Definitions.Def_QEC_Results_LocalityBounds_OptimalTradeoff
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
open Coding.StabilizerCode.StabilizerParameterData
universe u v

theorem QEC.Locality.exists_daiLi_optimal_locality_tradeoff :
    ∃ c0 c1 : ℝ, 0 < c0 ∧ 0 < c1 ∧
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] {κ : Type v} [Fintype κ]
        (D : StabilizerParameterData (ι := ι) (κ := κ))
        (embedding : UnitSeparatedEmbedding2D ι),
        c1 * (D.blockLength : ℝ) ≤
            (D.encodedQubits : ℝ) * (D.distance : ℝ) ^ 2 →
          c0 * max (D.encodedQubits : ℝ) (D.distance : ℝ) ≤
            (D.presentation.longInteractionCount embedding
              (c0 * max ((D.distance : ℝ) / Real.sqrt (D.blockLength : ℝ))
                (daiLiFourthRoot
                  ((D.encodedQubits : ℝ) * (D.distance : ℝ) ^ 2 /
                    (D.blockLength : ℝ)))) : ℝ) := by sorry
