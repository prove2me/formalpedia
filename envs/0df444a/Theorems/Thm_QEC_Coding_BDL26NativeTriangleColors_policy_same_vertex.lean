-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_policy_same_vertex
-- name    : QEC.Coding.BDL26NativeTriangleColors.policy_same_vertex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T04:43:05.390306+00:00
-- url     : https://prove2.me/theorems/9eb20573-cee1-4a42-b29b-6f6adbad83df
-- title:
--   BDL26 Native Triangle Colors: policy same vertex
-- statement:
--   The BDL26 Native Triangle Colors construction uses the policy same vertex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleColors.lean#L59-L72
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleColors.lean#L59-L72

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

theorem QEC.Coding.BDL26NativeTriangleColors.policy_same_vertex (hk : Function.Injective key) {a b : Triangle P}
    (hc : policyColor P key a=policyColor P key b) {i j : Fin 3}
    (hv : triangleVertex P a i=triangleVertex P b j) : a=b := by sorry
