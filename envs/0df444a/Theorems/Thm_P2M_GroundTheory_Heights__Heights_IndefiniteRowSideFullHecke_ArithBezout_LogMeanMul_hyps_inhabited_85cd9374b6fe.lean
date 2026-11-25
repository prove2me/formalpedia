-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ArithBezout_LogMeanMul_hyps_inhabited_85cd9374b6fe
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ArithBezout_LogMeanMul_hyps_inhabited_85cd9374b6fe
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:25:05.906262+00:00
-- url     : https://prove2.me/theorems/6dc0aebc-ce04-59a0-b9ba-2a1b3734eb7b
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Arith Bezout Log Mean Mul hyps inhabited 85cd9374b6fe: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Arith Bezou
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Arith Bezout Log Mean Mul hyps inhabited 85cd9374b6fe construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Arith Bezout Log Mean Mul hyps inhabited 85cd9374b6fe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SpecFirstDetFormNeZero.lean#L356-L358
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SpecFirstDetFormNeZero.lean#L356-L358

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LatticePointLogCount
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DegreeGeneric_hyps_inhabited_36d80aab7c4b

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ArithBezout
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Matrix

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ArithBezout_LogMeanMul_hyps_inhabited_85cd9374b6fe :
    IsUnit (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧ detForm ℂ ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ArithBezout».«LogMeanMul».«hyps_inhabited» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ArithBezout_LogMeanMul_hyps_inhabited_85cd9374b6fe
