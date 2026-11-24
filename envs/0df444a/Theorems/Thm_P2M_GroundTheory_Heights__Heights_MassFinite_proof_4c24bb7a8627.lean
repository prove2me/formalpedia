-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MassFinite_proof_4c24bb7a8627
-- name    : P2M_GroundTheory_Heights__Heights_MassFinite_proof_4c24bb7a8627
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T23:56:38.962242+00:00
-- url     : https://prove2.me/theorems/3bc49b6d-3eef-4982-a518-112b4d52b5a7
-- title:
--   P2 M Ground Theory Heights  Heights Mass Finite proof 4c24bb7a8627: P2 M Ground Theory Heights  Heights Mass Finite proof 4c24bb7a8627
-- statement:
--   The P2 M Ground Theory Heights  Heights Mass Finite proof 4c24bb7a8627 construction uses the P2 M Ground Theory Heights  Heights Mass Finite proof 4c24bb7a8627 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMassFinite.lean#L177-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMassFinite.lean#L177-L232

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalGraphMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMassFinite
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
open MvPolynomial MeasureTheory Matrix
open scoped ENNReal
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_MassFinite_proof_4c24bb7a8627 (hG : ComplexSets.GenericProjectionFinite.Statement)
    (hF : ComplexSets.FibreBound.Statement) (hD : ComplexSets.DiscriminantCover.Statement)
    (hN : NullSmaller.Statement) (hL : LocalGraphMass.Statement) : MassFinite.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MassFinite».«proof» := P2M_GroundTheory_Heights__Heights_MassFinite_proof_4c24bb7a8627
