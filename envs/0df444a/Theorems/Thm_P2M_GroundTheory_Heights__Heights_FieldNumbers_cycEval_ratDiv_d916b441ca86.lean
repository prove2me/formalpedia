-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_cycEval_ratDiv_d916b441ca86
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_cycEval_ratDiv_d916b441ca86
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:01:38.209509+00:00
-- url     : https://prove2.me/theorems/e96a04e8-31cd-45be-a6f1-1ac319c9a975
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers cyc Eval rat Div d916b441ca86: P2 M Ground Theory Heights  Heights Field Numbers cyc Eval rat Div d916b441ca86
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers cyc Eval rat Div d916b441ca86 construction uses the P2 M Ground Theory Heights  Heights Field Numbers cyc Eval rat Div d916b441ca86 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PCutRational.lean#L22-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PCutRational.lean#L22-L29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PCutRational
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open GroundTheory.Heights₂.Heights.NumbersDVR
universe u

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_cycEval_ratDiv_d916b441ca86 {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K]
    {ι : K → Type} [∀ k, Fintype (ι k)] (N : Ideal (MRing ι F) → ℤ) (P : Ideal (MRing ι F))
    (f g : MRing ι F) :
    cycEval N (ratDiv P f g) = cycEval N (divCycle P f) - cycEval N (divCycle P g) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«cycEval_ratDiv» := P2M_GroundTheory_Heights__Heights_FieldNumbers_cycEval_ratDiv_d916b441ca86
