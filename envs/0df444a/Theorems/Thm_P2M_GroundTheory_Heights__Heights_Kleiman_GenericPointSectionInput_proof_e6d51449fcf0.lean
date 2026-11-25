-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_GenericPointSectionInput_proof_e6d51449fcf0
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_GenericPointSectionInput_proof_e6d51449fcf0
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:08:49.769073+00:00
-- url     : https://prove2.me/theorems/f76f53ae-fcca-4484-8e47-6b12926793dd
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Generic Point Section Input proof e6d51449fcf0: P2 M Ground Theory Heights  Heights Kleiman Generic Point Section Input proof e6d51449fcf0
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Generic Point Section Input proof e6d51449fcf0 construction uses the P2 M Ground Theory Heights  Heights Kleiman Generic Point Section Input proof e6d51449fcf0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/InterSumEventuallyEqInterNum.lean#L75-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/InterSumEventuallyEqInterNum.lean#L75-L86

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StInterNumEventual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StInterNumAdditive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StInterNumCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StInterNumPointDeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_InterSumEventuallyEqInterNum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
noncomputable section
universe u w

theorem P2M_GroundTheory_Heights__Heights_Kleiman_GenericPointSectionInput_proof_e6d51449fcf0 (hE : InterNumEventual.Statement.{u, w})
    (hA : InterNumAdditive.Statement.{u, w}) (hC : InterNumCut.Statement.{u, w})
    (hP : InterNumPointDeg.Statement.{u, w}) : GenericPointSectionInput.Statement.{u, w} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«GenericPointSectionInput».«proof» := P2M_GroundTheory_Heights__Heights_Kleiman_GenericPointSectionInput_proof_e6d51449fcf0
