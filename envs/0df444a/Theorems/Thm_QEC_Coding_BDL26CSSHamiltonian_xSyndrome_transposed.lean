-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_xSyndrome_transposed
-- name    : QEC.Coding.BDL26CSSHamiltonian.xSyndrome_transposed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:02:58.492262+00:00
-- url     : https://prove2.me/theorems/066ecce8-21cc-4259-b9f8-79b8d93ca609
-- title:
--   BDL26 CSSHamiltonian: x Syndrome transposed
-- statement:
--   Literal transposed presentation, on the very same physical carrier.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/Rows.lean#L74-L80
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/Rows.lean#L74-L80

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

theorem QEC.Coding.BDL26CSSHamiltonian.xSyndrome_transposed : xSyndrome S n = tannerCoboundary1 (transposePresentation (presentation S n)) := by sorry
