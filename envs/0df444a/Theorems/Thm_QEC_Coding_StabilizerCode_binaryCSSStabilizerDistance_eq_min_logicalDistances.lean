-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_binaryCSSStabilizerDistance_eq_min_logicalDistances
-- name    : QEC.Coding.StabilizerCode.binaryCSSStabilizerDistance_eq_min_logicalDistances
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:43:49.872526+00:00
-- url     : https://prove2.me/theorems/62bb5097-fa8c-4522-b59b-5dedbfb7fec6
-- title:
--   Stabilizer Code: binary CSSStabilizer Distance eq min logical Distances
-- statement:
--   The semantic distance of a source-valid parity-check CSS code is the minimum
--   of its two attained relative logical-sector distances.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/Distance.lean#L169-L241
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/Distance.lean#L169-L241

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

theorem QEC.Coding.StabilizerCode.binaryCSSStabilizerDistance_eq_min_logicalDistances
    (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
    (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
    (horth : ∀ p q, wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)
    {dX dZ : Nat}
    (hX : CSSXLogicalMinimumDistance P Q dX)
    (hZ : CSSZLogicalMinimumDistance P Q dZ) :
    SemanticStabilizerDistance
      (binaryCSSSourceValidStabilizerOfParityChecks P Q horth) (min dX dZ) := by sorry
