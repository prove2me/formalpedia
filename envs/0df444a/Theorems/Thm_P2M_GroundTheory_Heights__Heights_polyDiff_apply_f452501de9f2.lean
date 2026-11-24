-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_polyDiff_apply_f452501de9f2
-- name    : P2M_GroundTheory_Heights__Heights_polyDiff_apply_f452501de9f2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:10.507822+00:00
-- url     : https://prove2.me/theorems/0568f376-a4f8-48ed-a437-e94cb1a81cbe
-- title:
--   P2 M Ground Theory Heights  Heights poly Diff apply f452501de9f2: P2 M Ground Theory Heights  Heights poly Diff apply f452501de9f2
-- statement:
--   The P2 M Ground Theory Heights  Heights poly Diff apply f452501de9f2 construction uses the P2 M Ground Theory Heights  Heights poly Diff apply f452501de9f2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PPolyLocalGeneratorsDiff.lean#L18-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PPolyLocalGeneratorsDiff.lean#L18-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsPolyLocalGenerators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPolyLocalGeneratorsDiff
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
open MvPolynomial Module
noncomputable section
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_polyDiff_apply_f452501de9f2 (p : Fin n → ℂ) (f : MvPolynomial (Fin n) ℂ) (j : Fin n) :
    polyDiff p f j = eval p (pderiv j f) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«polyDiff_apply» := P2M_GroundTheory_Heights__Heights_polyDiff_apply_f452501de9f2
