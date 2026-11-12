-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXCohomology_gauge_choice_independent
-- name    : QEC.Coding.BDL26RXCohomology.gauge_choice_independent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T05:44:58.098928+00:00
-- url     : https://prove2.me/theorems/4c9e8aff-6388-4124-8b4c-a765ee94aa2b
-- title:
--   BDL26 RXCohomology: gauge choice independent
-- statement:
--   Different local gauge potentials yield old words differing by an actual
--   old coboundary, rather than merely agreeing on a Q-sector readout.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXCohomology/Equivalence.lean#L224-L237
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXCohomology/Equivalence.lean#L224-L237

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Geometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Equivalence
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXCohomology
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementCochainMaps BDL26RXDecoderAdapter BDL26ReplacementSupport
open BDL26RZMap1CoordinateBridge
open MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXCohomology.gauge_choice_independent (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale)
    (w : Cocycle (rxReplacementPresentation P S)) (u v : Cocycle P)
    (f g : Word Field (RX0 P S))
    (hf : rxMap1Coord P S u.1 = coordinateWord P S w.1 - rxCoboundary0 P S f)
    (hg : rxMap1Coord P S v.1 = coordinateWord P S w.1 - rxCoboundary0 P S g) :
    u.1 - v.1 ∈ (complex P).firstCoboundaryCheckCode.carrier := by sorry
