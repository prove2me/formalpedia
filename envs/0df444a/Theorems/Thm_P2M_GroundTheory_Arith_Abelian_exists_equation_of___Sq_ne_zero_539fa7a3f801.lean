-- Prove2me | Theorems.Thm_P2M_GroundTheory_Arith_Abelian_exists_equation_of___Sq_ne_zero_539fa7a3f801
-- name    : P2M_GroundTheory_Arith_Abelian_exists_equation_of___Sq_ne_zero_539fa7a3f801
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:39:36.77036+00:00
-- url     : https://prove2.me/theorems/8c4ea291-4ec0-4920-85fb-aa069d14a46c
-- title:
--   P2 M Ground Theory Arith Abelian exists equation of   Sq ne zero 539fa7a3f801: P2 M Ground Theory Arith Abelian exists equation of   Sq ne zero 539fa7a3f801
-- statement:
--   The P2 M Ground Theory Arith Abelian exists equation of   Sq ne zero 539fa7a3f801 construction uses the P2 M Ground Theory Arith Abelian exists equation of   Sq ne zero 539fa7a3f801 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/KernelCard.lean#L12-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/KernelCard.lean#L12-L44

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

theorem P2M_GroundTheory_Arith_Abelian_exists_equation_of___Sq_ne_zero_539fa7a3f801 [IsSepClosed F] {x : F} (hx : W.Ψ₂Sq.eval x ≠ 0) :
    ∃ y, W.toAffine.Equation x y := by sorry

alias «GroundTheory».«Arith».«Abelian».«exists_equation_of_Ψ₂Sq_ne_zero» := P2M_GroundTheory_Arith_Abelian_exists_equation_of___Sq_ne_zero_539fa7a3f801
