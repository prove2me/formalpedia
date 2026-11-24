-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualArithmeticVariety_evalForm_ne_zero_eeeb6c3d9f4a
-- name    : P2M_GroundTheory_Heights__Heights_DualArithmeticVariety_evalForm_ne_zero_eeeb6c3d9f4a
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:10:33.815301+00:00
-- url     : https://prove2.me/theorems/eef3411f-388e-42d1-9c29-ad125ba51796
-- title:
--   P2 M Ground Theory Heights  Heights Dual Arithmetic Variety eval Form ne zero eeeb6c3d9f4a: P2 M Ground Theory Heights  Heights Dual Arithmetic Variety eval Form ne zero eeeb6c3d9f4a
-- statement:
--   The P2 M Ground Theory Heights  Heights Dual Arithmetic Variety eval Form ne zero eeeb6c3d9f4a construction uses the P2 M Ground Theory Heights  Heights Dual Arithmetic Variety eval Form ne zero eeeb6c3d9f4a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualArithVar.lean#L25-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualArithVar.lean#L25-L30

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLineDegreeDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualArithVar
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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.DualArithmeticVariety
variable {K : Type} [Field K]

theorem P2M_GroundTheory_Heights__Heights_DualArithmeticVariety_evalForm_ne_zero_eeeb6c3d9f4a {m : ℕ} {φ : Fin m → K} (hφ : φ ≠ 0) : evalForm m φ ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DualArithmeticVariety».«evalForm_ne_zero» := P2M_GroundTheory_Heights__Heights_DualArithmeticVariety_evalForm_ne_zero_eeeb6c3d9f4a
