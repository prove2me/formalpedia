-- Prove2me | Theorems.Thm_QEC_Locality_daiLiLargeDistance_fewLongInteractions_encodedQubits_eq_zero
-- name    : QEC.Locality.daiLiLargeDistance_fewLongInteractions_encodedQubits_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:08:32.216427+00:00
-- url     : https://prove2.me/theorems/98f30c1f-cc0d-4a1e-9cf4-d0737fe90217
-- title:
--   Locality: dai Li Large Distance few Long Interactions encoded Qubits eq zero
-- statement:
--   DL24 Part I's actual recursive-separator contradiction.  The source's
--   large-distance inequality is retained as an explicit branch condition; the
--   Part-I argument itself proves the stronger statement using its finite
--   above-BPT hypothesis and never assumes a separator, a recovery, or an
--   interaction-count conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/LargeDistanceSeparator.lean#L2579-L2639
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/LargeDistanceSeparator.lean#L2579-L2639

import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Definitions.Def_QEC_Locality_CorrectableRegions_TwoCorrectableRegionsDimension
import Definitions.Def_QEC_Locality_OptimalTradeoff_LargeDistanceSeparator
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]

theorem QEC.Locality.daiLiLargeDistance_fewLongInteractions_encodedQubits_eq_zero
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : Nat)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (hAboveBPT : 100 * Fintype.card ι ≤ P.encodedQubits * d ^ 2)
    (hLargeDistance : Real.sqrt ((P.encodedQubits : ℝ) * (Fintype.card ι : ℝ)) ≤ d)
    (hFew : DaiLiLargeDistanceFewLongInteractions P embedding d) :
    P.encodedQubits = 0 := by sorry
