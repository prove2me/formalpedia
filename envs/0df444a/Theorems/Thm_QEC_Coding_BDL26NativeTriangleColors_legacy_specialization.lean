-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_legacy_specialization
-- name    : QEC.Coding.BDL26NativeTriangleColors.legacy_specialization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T08:15:05.947273+00:00
-- url     : https://prove2.me/theorems/09afdf00-ae3a-4a93-85f5-cfef6a0a819d
-- title:
--   BDL26 Native Triangle Colors: legacy specialization
-- statement:
--   Literal specialization; no existing definition is rewritten.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleColors.lean#L90-L91
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleColors.lean#L90-L91

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeSupportMetadata
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleColors
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleColors
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RandomPerturbation BDL26BoundedValence
open G
noncomputable section
variable (P : TannerSquarePresentation) (key : Triangle P → ℕ)

theorem QEC.Coding.BDL26NativeTriangleColors.legacy_specialization (t : Triangle P) :
    policyColor P (triangleKey P) t=triangleColor P t := by sorry
