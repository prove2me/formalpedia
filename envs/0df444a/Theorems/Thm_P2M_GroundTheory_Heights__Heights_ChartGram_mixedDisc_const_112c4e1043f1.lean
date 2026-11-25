-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartGram_mixedDisc_const_112c4e1043f1
-- name    : P2M_GroundTheory_Heights__Heights_ChartGram_mixedDisc_const_112c4e1043f1
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:26:53.802456+00:00
-- url     : https://prove2.me/theorems/9bd4072c-f35d-49b6-835e-090f9c0d4383
-- title:
--   P2 M Ground Theory Heights  Heights Chart Gram mixed Disc const 112c4e1043f1: P2 M Ground Theory Heights  Heights Chart Gram mixed Disc const 112c4e1043f1
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Gram mixed Disc const 112c4e1043f1 construction uses the P2 M Ground Theory Heights  Heights Chart Gram mixed Disc const 112c4e1043f1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ChartGramPolar.lean#L24-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ChartGramPolar.lean#L24-L34

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChartGramPolar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Finset
open ReciprocityTheory.ChartRestriction.G.Geo (mixedDisc)

theorem P2M_GroundTheory_Heights__Heights_ChartGram_mixedDisc_const_112c4e1043f1 {D : ℕ} (A : Matrix (Fin D) (Fin D) ℂ) :
    mixedDisc (fun _ => A) = A.det := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartGram».«mixedDisc_const» := P2M_GroundTheory_Heights__Heights_ChartGram_mixedDisc_const_112c4e1043f1
