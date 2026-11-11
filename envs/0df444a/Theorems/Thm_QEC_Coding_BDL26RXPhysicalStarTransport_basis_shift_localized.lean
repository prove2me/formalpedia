-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_basis_shift_localized
-- name    : QEC.Coding.BDL26RXPhysicalStarTransport.basis_shift_localized
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:35:08.988415+00:00
-- url     : https://prove2.me/theorems/747d9d0c-f86a-4205-8f75-20ac9725a4ca
-- title:
--   BDL26 RXPhysical Star Transport: basis shift localized
-- statement:
--   The BDL26 RXPhysical Star Transport construction uses the basis shift localized property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L359-L369
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L359-L369

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPhysicalStarTransport
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXPhysicalStarTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge BDL26RXXStarTransport
open BDL26RXLocalReplacement BDL26ReplacementSupport MultiscaleDecoder
open RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)

theorem QEC.Coding.BDL26RXPhysicalStarTransport.basis_shift_localized (p : FamilyQ S depth i.succ) (a : Upper S depth i) :
    Localized S depth i (perturbationCenter S depth i p) a (a+canonicalBasisWord p) := by sorry
