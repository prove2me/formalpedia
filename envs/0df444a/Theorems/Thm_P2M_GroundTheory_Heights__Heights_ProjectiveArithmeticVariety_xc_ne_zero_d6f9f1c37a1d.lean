-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjectiveArithmeticVariety_xc_ne_zero_d6f9f1c37a1d
-- name    : P2M_GroundTheory_Heights__Heights_ProjectiveArithmeticVariety_xc_ne_zero_d6f9f1c37a1d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:15.177904+00:00
-- url     : https://prove2.me/theorems/e8ae2568-de01-40a0-90f9-8364db1a54fe
-- title:
--   P2 M Ground Theory Heights  Heights Projective Arithmetic Variety xc ne zero d6f9f1c37a1d: P2 M Ground Theory Heights  Heights Projective Arithmetic Variety xc ne zero d6f9f1c37a1d
-- statement:
--   The P2 M Ground Theory Heights  Heights Projective Arithmetic Variety xc ne zero d6f9f1c37a1d construction uses the P2 M Ground Theory Heights  Heights Projective Arithmetic Variety xc ne zero d6f9f1c37a1d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PProjArithVar.lean#L21-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PProjArithVar.lean#L21-L22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLineDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PProjArithVar
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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.ProjectiveArithmeticVariety
variable (K : Type) [Field K] [NumberField K] (n : ℕ)
omit [NumberField K]

theorem P2M_GroundTheory_Heights__Heights_ProjectiveArithmeticVariety_xc_ne_zero_d6f9f1c37a1d (j : Fin (n + 1)) : xc K n j ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ProjectiveArithmeticVariety».«xc_ne_zero» := P2M_GroundTheory_Heights__Heights_ProjectiveArithmeticVariety_xc_ne_zero_d6f9f1c37a1d
