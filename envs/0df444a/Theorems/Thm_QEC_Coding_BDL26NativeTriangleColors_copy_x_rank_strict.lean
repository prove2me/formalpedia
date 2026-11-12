-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_copy_x_rank_strict
-- name    : QEC.Coding.BDL26NativeTriangleColors.copy_x_rank_strict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T08:33:55.3006+00:00
-- url     : https://prove2.me/theorems/33ffed65-0835-4ba9-ad76-efa70c41ebdf
-- title:
--   BDL26 Native Triangle Colors: copy x rank strict
-- statement:
--   The two native copies share X, hence their X-fiber ranks strictly increase.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleColors.lean#L398-L406
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleColors.lean#L398-L406

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeSupportMetadata
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleColors
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleColors
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RandomPerturbation BDL26BoundedValence
open G
noncomputable section
open scoped Classical

theorem QEC.Coding.BDL26NativeTriangleColors.copy_x_rank_strict (S : OddScale) (n : ℕ) (f : (P S n).Face) :
    nativeColor S n (f,0) 0<nativeColor S n (f,1) 0 := by sorry
