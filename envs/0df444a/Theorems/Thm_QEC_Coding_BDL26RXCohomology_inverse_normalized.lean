-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXCohomology_inverse_normalized
-- name    : QEC.Coding.BDL26RXCohomology.inverse_normalized
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T05:45:55.305111+00:00
-- url     : https://prove2.me/theorems/9193c87f-93dc-44f3-b9eb-a9a6fa301de9
-- title:
--   BDL26 RXCohomology: inverse normalized
-- statement:
--   Inverse action on every actual zero-X cocycle uses the genuine cone-point
--   readout on both connected copies.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXCohomology/Equivalence.lean#L241-L255
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXCohomology/Equivalence.lean#L241-L255

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Geometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Equivalence
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXCohomology
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementCochainMaps BDL26RXDecoderAdapter BDL26ReplacementSupport
open BDL26RZMap1CoordinateBridge
open MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXCohomology.inverse_normalized (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale)
    (w : Cocycle (rxReplacementPresentation P S))
    (hx : ∀ x, restrictWordLinear ((localX P S).correctionRegion x) w.1 = 0) :
    ∃ v : Cocycle P, v.1 = coarseWord P S w.1 ∧
      (equiv P A R S).symm (classOf (rxReplacementPresentation P S) w) = classOf P v := by sorry
