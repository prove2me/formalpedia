-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalizedHistoryErrorDescent_depth_two
-- name    : QEC.Coding.BDL26LocalizedHistoryErrorDescent.depth_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T18:15:26.717965+00:00
-- url     : https://prove2.me/theorems/6d76b086-2f00-4094-8956-191275d76979
-- title:
--   BDL26 Localized History Error Descent: depth two
-- statement:
--   Physical C2 is literally unchanged; h=e and P=0 at suffix depth zero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalizedHistoryErrorDescent.lean#L909-L915
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalizedHistoryErrorDescent.lean#L909-L915

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalizedHistoryErrorDescent
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LocalizedHistoryErrorDescent
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open scoped Classical BigOperators
variable (S : OddScale) (n : Nat) (sigma tau : TopInput S n)
variable (top : LocalizedWord S n sigma tau (TopIndex n))

theorem QEC.Coding.BDL26LocalizedHistoryErrorDescent.depth_two (S : OddScale) (sigma : TopInput S 0)
    (e : (Data S 0).family.Cochain1 (TopIndex 0))
    (x : (state S 2).presentation.X) (he : hammingSupport e⊆star S 0 (TopIndex 0) x) :
    (actualDescent S 0 sigma e x he 0).word=e ∧ actualPotential S 0 sigma e x he 0 0=0 := by sorry
