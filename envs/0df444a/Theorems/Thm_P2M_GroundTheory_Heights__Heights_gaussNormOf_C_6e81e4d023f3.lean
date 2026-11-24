-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_gaussNormOf_C_6e81e4d023f3
-- name    : P2M_GroundTheory_Heights__Heights_gaussNormOf_C_6e81e4d023f3
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:53:46.543886+00:00
-- url     : https://prove2.me/theorems/19e02e4c-f349-48c4-9395-18dc34f07fab
-- title:
--   P2 M Ground Theory Heights  Heights gauss Norm Of C 6e81e4d023f3: P2 M Ground Theory Heights  Heights gauss Norm Of C 6e81e4d023f3
-- statement:
--   The P2 M Ground Theory Heights  Heights gauss Norm Of C 6e81e4d023f3 construction uses the P2 M Ground Theory Heights  Heights gauss Norm Of C 6e81e4d023f3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogGaussNormSupportFinite.lean#L58-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogGaussNormSupportFinite.lean#L58-L67

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField
noncomputable section
variable {R : Type*} [CommRing R] {ι : Type*} (w : AbsoluteValue R ℝ)

theorem P2M_GroundTheory_Heights__Heights_gaussNormOf_C_6e81e4d023f3 (c : R) : gaussNormOf w (C c : MvPolynomial ι R) = w c := by sorry

alias «GroundTheory».«Heights₂».«Heights».«gaussNormOf_C» := P2M_GroundTheory_Heights__Heights_gaussNormOf_C_6e81e4d023f3
