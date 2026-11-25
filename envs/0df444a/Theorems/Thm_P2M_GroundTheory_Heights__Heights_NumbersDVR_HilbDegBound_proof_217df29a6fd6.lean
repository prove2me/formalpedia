-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HilbDegBound_proof_217df29a6fd6
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_HilbDegBound_proof_217df29a6fd6
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:29:46.984799+00:00
-- url     : https://prove2.me/theorems/a3e77161-5d1b-48cc-b817-02263b7d9a71
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Hilb Deg Bound proof 217df29a6fd6: P2 M Ground Theory Heights  Heights Numbers DVR Hilb Deg Bound proof 217df29a6fd6
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Hilb Deg Bound proof 217df29a6fd6 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Hilb Deg Bound proof 217df29a6fd6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PHilbDegBound.lean#L101-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PHilbDegBound.lean#L101-L174

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PHilbDegBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
open HilbDegBound

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_HilbDegBound_proof_217df29a6fd6 (h1 : HilbFnVanishBlock.Statement.{u}) (h2 : HilbFnCut.Statement.{u})
    (h3 : PrimeFiltration.Statement.{u}) (h4 : DimStrictDrop.Statement.{u})
    (h5 : RelevantDimGe.Statement.{u}) (h6 : DegLTClosure.Statement)
    (h7 : DegLTOfUnitSteps.Statement) : HilbDegBound.Statement.{u} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«HilbDegBound».«proof» := P2M_GroundTheory_Heights__Heights_NumbersDVR_HilbDegBound_proof_217df29a6fd6
