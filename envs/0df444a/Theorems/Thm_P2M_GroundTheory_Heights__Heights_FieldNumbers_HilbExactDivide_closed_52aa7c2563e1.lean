-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbExactDivide_closed_52aa7c2563e1
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbExactDivide_closed_52aa7c2563e1
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T23:53:45.616937+00:00
-- url     : https://prove2.me/theorems/7a2175e5-f5c1-4ed3-aed1-697017a685fb
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Hilb Exact Divide closed 52aa7c2563e1: P2 M Ground Theory Heights  Heights Field Numbers Hilb Exact Divide closed 52aa7c2563e1
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Hilb Exact Divide closed 52aa7c2563e1 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Hilb Exact Divide closed 52aa7c2563e1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PHilbExactDivide.lean#L192-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PHilbExactDivide.lean#L192-L193

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PGradedFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PHilbExactDivide
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
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.HilbExactDivide
variable {K : Type} [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]
attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbExactDivide_closed_52aa7c2563e1 : HilbExactDivide.Statement.{u} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«HilbExactDivide».«closed» := P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbExactDivide_closed_52aa7c2563e1
