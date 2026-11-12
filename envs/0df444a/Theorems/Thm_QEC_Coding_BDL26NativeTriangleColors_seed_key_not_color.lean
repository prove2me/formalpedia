-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_seed_key_not_color
-- name    : QEC.Coding.BDL26NativeTriangleColors.seed_key_not_color
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T08:35:31.727278+00:00
-- url     : https://prove2.me/theorems/74b20d1c-557f-4aae-a516-1d8239b607ac
-- title:
--   BDL26 Native Triangle Colors: seed key not color
-- statement:
--   Actual seed face2/copy0 has dense key4 but first rank0 in its X fiber.
--   The key and a bounded local color are therefore different quantities.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleColors.lean#L619-L642
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleColors.lean#L619-L642

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

theorem QEC.Coding.BDL26NativeTriangleColors.seed_key_not_color (S : OddScale) :
    nativeKey S 0 ((2 : Fin 4),(0 : Fin 2))=4 ∧
      nativeColor S 0 ((2 : Fin 4),(0 : Fin 2)) 0=0 := by sorry
