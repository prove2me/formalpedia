-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_binaryCSSStabilizerDistance_eq_min_classicalDistances_of_strictPurity
-- name    : QEC.Coding.StabilizerCode.binaryCSSStabilizerDistance_eq_min_classicalDistances_of_strictPurity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:44:06.290877+00:00
-- url     : https://prove2.me/theorems/72427fe7-da1a-48ea-9102-8367d51dd661
-- title:
--   Stabilizer Code: binary CSSStabilizer Distance eq min classical Distances of strict Purity
-- statement:
--   Under strict generated-group purity at the ordinary threshold, the semantic
--   CSS distance is the minimum of the two ordinary nonzero kernel-code distances.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/Distance.lean#L247-L357
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/Distance.lean#L247-L357

import Definitions.Def_QEC_Coding_CSS_ParityChecks
import Definitions.Def_QEC_Coding_Stabilizer_Distance
import Definitions.Def_QEC_Coding_CSS_Distance
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open Classical
universe u v
open QEC.Coding.StabilizerCode
open PauliSymplectic
variable {ι κP κQ : Type v} [Fintype ι] [DecidableEq ι]
  [Fintype κP] [Fintype κQ]

theorem QEC.Coding.StabilizerCode.binaryCSSStabilizerDistance_eq_min_classicalDistances_of_strictPurity
    (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
    (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
    (horth : ∀ p q, wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)
    {dP dQ : Nat}
    (hP : MinimumDistance (parityCheckKernelCode P) dP)
    (hQ : MinimumDistance (parityCheckKernelCode Q) dQ)
    (hPurity : StrictGeneratedGroupPurity
      (binaryCSSStabilizerCodeOfParityChecks P Q horth) (min dP dQ)) :
    SemanticStabilizerDistance
      (binaryCSSSourceValidStabilizerOfParityChecks P Q horth) (min dP dQ) := by sorry
