-- Prove2me | Theorems.Thm_P2M_GroundTheory_Arith_Abelian__Sq_ne_zero_of_ne_zero_fd3fba5d47fb
-- name    : P2M_GroundTheory_Arith_Abelian__Sq_ne_zero_of_ne_zero_fd3fba5d47fb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:18:41.565012+00:00
-- url     : https://prove2.me/theorems/0ad0f642-02fe-49d7-8cdc-f0d4a47f566d
-- title:
--   P2 M Ground Theory Arith Abelian  Sq ne zero of ne zero fd3fba5d47fb: P2 M Ground Theory Arith Abelian  Sq ne zero of ne zero fd3fba5d47fb
-- statement:
--   The P2 M Ground Theory Arith Abelian  Sq ne zero of ne zero fd3fba5d47fb construction uses the P2 M Ground Theory Arith Abelian  Sq ne zero of ne zero fd3fba5d47fb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/KernelCard.lean#L109-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/KernelCard.lean#L109-L117

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisionPoints
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_KernelCard
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
variable {F : Type*} [Field F] (W : WeierstrassCurve F)
variable [W.IsElliptic]

theorem P2M_GroundTheory_Arith_Abelian__Sq_ne_zero_of_ne_zero_fd3fba5d47fb {n : ℤ} (hn : n ≠ 0) : W.ΨSq n ≠ 0 := by sorry

alias «GroundTheory».«Arith».«Abelian».«ΨSq_ne_zero_of_ne_zero» := P2M_GroundTheory_Arith_Abelian__Sq_ne_zero_of_ne_zero_fd3fba5d47fb
