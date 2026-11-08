-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_rzCqBottomCoboundary_eq_boundary1
-- name    : QEC.Coding.BDL26RZLocalReplacement.rzCqBottomCoboundary_eq_boundary1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T14:05:04.362276+00:00
-- url     : https://prove2.me/theorems/f1418adf-bf13-4fe2-a5c0-9db235af3725
-- title:
--   BDL26 RZLocal Replacement: rz Cq Bottom Coboundary eq boundary1
-- statement:
--   The concrete bottom coboundary of the Q-local dual block is the original
--   Q-cylinder graph boundary.  This keeps the auxiliary `H⁰(Cq)` carrier tied to
--   the actual local complex rather than introducing a parallel kernel.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZLocalReplacement.lean#L17000-L17005
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZLocalReplacement.lean#L17000-L17005

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalRegularity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZLocalReplacement
set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.BDL26RZLocalReplacement
open BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity

theorem QEC.Coding.BDL26RZLocalReplacement.rzCqBottomCoboundary_eq_boundary1 (P : TannerSquarePresentation)
    (q : P.Q) (S : OddScale) :
    wordLinearMapTranspose (rzCq P q S).boundary1 =
      qDoubleCylinderBoundary1 (transposePresentation P) q S := by sorry
