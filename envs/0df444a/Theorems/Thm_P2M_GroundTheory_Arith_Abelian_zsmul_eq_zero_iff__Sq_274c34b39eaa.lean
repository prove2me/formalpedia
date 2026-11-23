-- Prove2me | Theorems.Thm_P2M_GroundTheory_Arith_Abelian_zsmul_eq_zero_iff__Sq_274c34b39eaa
-- name    : P2M_GroundTheory_Arith_Abelian_zsmul_eq_zero_iff__Sq_274c34b39eaa
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:39:49.420689+00:00
-- url     : https://prove2.me/theorems/b3d8dbb9-85a1-47c5-a875-1c615c3d7e74
-- title:
--   P2 M Ground Theory Arith Abelian zsmul eq zero iff  Sq 274c34b39eaa: P2 M Ground Theory Arith Abelian zsmul eq zero iff  Sq 274c34b39eaa
-- statement:
--   The P2 M Ground Theory Arith Abelian zsmul eq zero iff  Sq 274c34b39eaa construction uses the P2 M Ground Theory Arith Abelian zsmul eq zero iff  Sq 274c34b39eaa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/KernelCard.lean#L344-L355
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/KernelCard.lean#L344-L355

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
variable {F : Type*} [Field F] [IsSepClosed F] [DecidableEq F] (W : WeierstrassCurve F)
  [W.IsElliptic]
omit [IsSepClosed F] [W.IsElliptic]

theorem P2M_GroundTheory_Arith_Abelian_zsmul_eq_zero_iff__Sq_274c34b39eaa (n : ℤ) (P : W.toAffine.Point) :
    n • P = 0 ↔ P = 0 ∨ ∃ (x y : F) (h : W.toAffine.Nonsingular x y),
      P = .some x y h ∧ (W.ΨSq n).eval x = 0 := by sorry

alias «GroundTheory».«Arith».«Abelian».«zsmul_eq_zero_iff_ΨSq» := P2M_GroundTheory_Arith_Abelian_zsmul_eq_zero_iff__Sq_274c34b39eaa
