-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbDegreeBound_proof_bc085c65b8cd
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbDegreeBound_proof_bc085c65b8cd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:40:44.736535+00:00
-- url     : https://prove2.me/theorems/fc483892-4713-44b4-b4d1-d842d564edcb
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Hilb Degree Bound proof bc085c65b8cd: P2 M Ground Theory Heights  Heights Field Numbers Hilb Degree Bound proof bc085c65b8cd
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Hilb Degree Bound proof bc085c65b8cd construction uses the P2 M Ground Theory Heights  Heights Field Numbers Hilb Degree Bound proof bc085c65b8cd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PHilbDegreeBound.lean#L212-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PHilbDegreeBound.lean#L212-L235

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegreeBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PHilbDegreeBound
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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbDegreeBound_proof_bc085c65b8cd (h1 : HilbEventuallyPoly.Statement.{u})
    (h2 : HilbExactDivide.Statement.{u}) (h3 : PolyOfDiffs.Statement)
    (h4 : PrimeFiltration.Statement.{u}) (hU : EventuallyPolyUnique.Statement)
    (hS : EventuallyPolyShift.Statement) (hZ : HilbIrrelevantZero.Statement.{u})
    (hD : RelevantPrimeDimGe.Statement.{u}) : HilbDegreeBound.Statement.{u} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«HilbDegreeBound».«proof» := P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbDegreeBound_proof_bc085c65b8cd
