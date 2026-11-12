-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalizedHistoryErrorDescent_source_even_history
-- name    : QEC.Coding.BDL26LocalizedHistoryErrorDescent.source_even_history
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T18:23:56.546409+00:00
-- url     : https://prove2.me/theorems/37a10d1c-179d-414a-92fa-b289f3b0db29
-- title:
--   BDL26 Localized History Error Descent: source even history
-- statement:
--   Source-even depth2k, k>=1, includes the empty suffix k=1 exactly.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalizedHistoryErrorDescent.lean#L892-L906
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalizedHistoryErrorDescent.lean#L892-L906

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

theorem QEC.Coding.BDL26LocalizedHistoryErrorDescent.source_even_history (S : OddScale) (k : Nat) (hk : 1≤k)
    (sigma : TopInput S (2*(k-1))) (q : (state S (2*(k-1)+2)).presentation.Q) :
    2*(k-1)+2=2*k ∧
    (let n := 2*(k-1)
     let e := canonicalBasisWord (F := BDL26Field) q
     let x := elementaryCenter S n q
     let he := elementary_support S n q
     e+historyLiftedCorrection (Data S n) (actualHistory S n sigma)+
       historyLiftedCorrection (Data S n) (actualHistory S n (perturbTop S n sigma e))=
       intervalMap1 (Data S n) 0 (TopIndex n) (Nat.zero_le _)
         ((actualDescent S n sigma e x he 0).word+
           (actualBase S n).decode (actualInputs S n sigma 0)+
           (actualBase S n).decode (actualInputs S n (perturbTop S n sigma e) 0))+
       (Data S n).family.coboundary0 (TopIndex n) (actualPotential S n sigma e x he 0 (TopIndex n))) := by sorry
