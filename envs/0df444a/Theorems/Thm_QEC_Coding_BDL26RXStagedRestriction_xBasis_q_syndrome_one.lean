-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXStagedRestriction_xBasis_q_syndrome_one
-- name    : QEC.Coding.BDL26RXStagedRestriction.xBasis_q_syndrome_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:42:54.749376+00:00
-- url     : https://prove2.me/theorems/e247330c-c3df-4b56-874e-cf5945c14b0f
-- title:
--   BDL26 RXStaged Restriction: x Basis q syndrome one
-- statement:
--   The actual X-to-Q matrix coefficient survives on the incident basis error.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXStagedRestriction.lean#L64-L74
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXStagedRestriction.lean#L64-L74

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementCochainMaps
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXStagedRestriction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXStagedRestriction
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26ReplacementSupport BDL26ReplacementCochainMaps
open MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXStagedRestriction.xBasis_q_syndrome_one (P : TannerSquarePresentation) (S : OddScale)
    (x : P.X) (q : P.Q) (h : P.xq x q = true) (a : QDoubleCylinderEdge P q S) :
    rxCoboundary1 P S
      (canonicalBasisWord (Sum.inl ⟨x,qToXDoubleCylinderEdgeRaw P q x h S a⟩))
      (Sum.inl (Sum.inr ⟨q,a⟩)) = 1 := by sorry
