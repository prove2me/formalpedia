-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_xRowCode
-- name    : QEC.Coding.BDL26CSSHamiltonian.xRowCode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:55:23.698899+00:00
-- url     : https://prove2.me/theorems/82799773-2840-49f0-8927-bce28fa05595
-- title:
--   BDL26 CSSHamiltonian: x Row Code
-- statement:
--   The BDL26 CSSHamiltonian construction uses the x Row Code property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/Rows.lean#L84-L86
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/Rows.lean#L84-L86

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_IndexedDecoder
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Gibbs
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Rows
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSHamiltonian
open Classical BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26DecodingGraph BDL26RZMap1CoordinateBridge BDL26LevelTwoDecoder
open PauliSymplectic Semantics
open scoped BigOperators
variable (S : OddScale) (n : Nat)

theorem QEC.Coding.BDL26CSSHamiltonian.xRowCode : parityCheckRowCode (xSyndrome S n) = (complex S n).firstCoboundaryCheckCode := by sorry
