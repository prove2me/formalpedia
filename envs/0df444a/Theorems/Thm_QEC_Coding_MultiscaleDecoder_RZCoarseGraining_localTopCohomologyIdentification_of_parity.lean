-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_RZCoarseGraining_localTopCohomologyIdentification_of_parity
-- name    : QEC.Coding.MultiscaleDecoder.RZCoarseGraining.localTopCohomologyIdentification_of_parity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:43:36.844964+00:00
-- url     : https://prove2.me/theorems/30fcfea6-dd00-430b-93ff-406bd18b770b
-- title:
--   RZCoarse Graining: local Top Cohomology Identification of parity
-- statement:
--   Construct the local top-cohomology identification from a parity map.
--
--   The equality of the local boundary range with the parity kernel is the only
--   quotient bookkeeping obligation left to a concrete RZ fixture.  Once that
--   equality and surjectivity are proved, Mathlib's first-isomorphism theorem
--   provides the required quotient equivalence.  The final hypothesis records the
--   coordinate formula for the parity map and keeps the source-facing statement
--   explicit rather than relying on reducibility of a fixture definition.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/RZCoarseGraining.lean#L196-L212
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/RZCoarseGraining.lean#L196-L212

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Multiscale
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RZCoarseGraining
set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.MultiscaleDecoder
open QEC.Coding.MultiscaleDecoder.RZCoarseGraining
open scoped BigOperators
universe u v
variable {depth : Nat}
variable {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)]
  [∀ i, Fintype (C2 i)]
variable [∀ i, DecidableEq (C1 i)] [∀ i, DecidableEq (C2 i)]
variable {D : BDL26DecoderData depth C0 C1 C2}
variable {i : StepIndex depth}
variable {V : Type v} [Fintype V] [DecidableEq V]
open RZCoarseGrainingData

theorem QEC.Coding.MultiscaleDecoder.RZCoarseGraining.localTopCohomologyIdentification_of_parity
    (A : RZCoarseGrainingData D i V)
    (parity : ∀ z : C2 i.castSucc, localTopSpace A z →ₗ[Field] Field)
    (hker : ∀ z, localBoundaryRange A z = LinearMap.ker (parity z))
    (hsurj : ∀ z, Function.Surjective (parity z))
    (hformula : ∀ z r,
      parity z r =
        (∑ p ∈ A.coarseRegion z,
          (r : D.family.Cochain2 i.succ) p)) :
    LocalTopCohomologyIdentification A := by sorry
