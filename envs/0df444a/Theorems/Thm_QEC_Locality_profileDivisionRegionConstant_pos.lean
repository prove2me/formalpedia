-- Prove2me | Theorems.Thm_QEC_Locality_profileDivisionRegionConstant_pos
-- name    : QEC.Locality.profileDivisionRegionConstant_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:51:49.671051+00:00
-- url     : https://prove2.me/theorems/056d8233-5ed6-4f1b-aa69-930d9756b3b3
-- title:
--   Locality: profile Division Region Constant pos
-- statement:
--   The fixed region constant is positive on the profile parameter range.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/StoppedPotential.lean#L552-L565
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/StoppedPotential.lean#L552-L565

import Definitions.Def_QEC_Locality_SeparatorProfile_DivisionPotential
import Definitions.Def_QEC_Locality_SeparatorProfile_Completion
import Definitions.Def_QEC_Locality_SeparatorProfile_StoppedPotential
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.profileDivisionRegionConstant_pos
    {beta exponent : ℝ} (hbeta : 1 ≤ beta)
    (hexponent : 0 < exponent ∧ exponent < 1) :
    0 < profileDivisionRegionConstant beta exponent := by sorry
