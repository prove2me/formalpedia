-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_legacy_bounded_specialization
-- name    : QEC.Coding.BDL26NativeTriangleColors.legacy_bounded_specialization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T08:15:09.336847+00:00
-- url     : https://prove2.me/theorems/bcb35a65-1e07-495c-b20c-b911624b1ced
-- title:
--   BDL26 Native Triangle Colors: legacy bounded specialization
-- statement:
--   The BDL26 Native Triangle Colors construction uses the legacy bounded specialization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleColors.lean#L93-L97
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleColors.lean#L93-L97

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

theorem QEC.Coding.BDL26NativeTriangleColors.legacy_bounded_specialization (hv : BoundedValence P) (t : Triangle P) :
    boundedPolicyColor P (triangleKey P) hv t=boundedTriangleColor P hv t := by sorry
