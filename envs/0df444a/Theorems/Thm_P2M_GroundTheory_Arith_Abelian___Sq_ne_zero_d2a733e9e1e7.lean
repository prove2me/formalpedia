-- Prove2me | Theorems.Thm_P2M_GroundTheory_Arith_Abelian___Sq_ne_zero_d2a733e9e1e7
-- name    : P2M_GroundTheory_Arith_Abelian___Sq_ne_zero_d2a733e9e1e7
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:19:29.23795+00:00
-- url     : https://prove2.me/theorems/5c3b7fc0-1b2a-45fb-b310-8945b179b26c
-- title:
--   P2 M Ground Theory Arith Abelian   Sq ne zero d2a733e9e1e7: P2 M Ground Theory Arith Abelian   Sq ne zero d2a733e9e1e7
-- statement:
--   The P2 M Ground Theory Arith Abelian   Sq ne zero d2a733e9e1e7 construction uses the P2 M Ground Theory Arith Abelian   Sq ne zero d2a733e9e1e7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/KernelCard.lean#L125-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/KernelCard.lean#L125-L138

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
variable {F : Type*} [Field F] (W : WeierstrassCurve F) [W.IsElliptic]

theorem P2M_GroundTheory_Arith_Abelian___Sq_ne_zero_d2a733e9e1e7 : W.Ψ₂Sq ≠ 0 := by sorry

alias «GroundTheory».«Arith».«Abelian».«Ψ₂Sq_ne_zero» := P2M_GroundTheory_Arith_Abelian___Sq_ne_zero_d2a733e9e1e7
