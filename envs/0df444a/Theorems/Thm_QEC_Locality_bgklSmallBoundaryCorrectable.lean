-- Prove2me | Theorems.Thm_QEC_Locality_bgklSmallBoundaryCorrectable
-- name    : QEC.Locality.bgklSmallBoundaryCorrectable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:14:36.781681+00:00
-- url     : https://prove2.me/theorems/65ff1975-5a77-4a47-bc63-d5b395f8f975
-- title:
--   Locality: bgkl Small Boundary Correctable
-- statement:
--   BGKL small-boundary correctability (`lem:correct-1`) for the fixed-generator
--   interaction graph.  The constants and ranges are the source constants:
--   `beta ≥ 1`, `0 < exponent < 1`, `0 < d ≤ n`,
--   `|W| ≤ (epsilon' d)^(1/exponent)`, and `|∂₊W| ≤ d/4`, where
--   `epsilon' = (1 - (2/3)^exponent) / (20 beta)`.
--
--   The conclusion contains the concrete CPTP recovery for erasure of `W`; it is
--   not a stored correctability assumption or a target tradeoff premise.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/SmallBoundary.lean#L702-L723
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/SmallBoundary.lean#L702-L723

import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Locality_SeparatorProfile_Core
import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding
open scoped BigOperators
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]

theorem QEC.Locality.bgklSmallBoundaryCorrectable
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (d : Nat) (hd : 0 < d) (hdn : d ≤ Fintype.card ι)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (beta exponent : ℝ)
    (hProfile : P.AssumedFixedGeneratorBGKLMeasuredProfilePowerUpperBound beta exponent)
    (hexponent : exponent < 1)
    (W : Finset ι)
    (hSmall : (W.card : ℝ) ≤ Real.rpow
      (bgklSmallBoundaryEpsilon beta exponent * d) exponent⁻¹)
    (hBoundary : 4 * (fixedGeneratorOuterBoundaryFinset P W).card ≤ d) :
    ∃ recovery : QuantumChannel (finiteSubsystemOfFinset W).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (finiteSubsystemOfFinset W).complementSystem P.semanticCode
        (finiteSubsystemOfFinset W).erasureChannelFromRegister recovery := by sorry
