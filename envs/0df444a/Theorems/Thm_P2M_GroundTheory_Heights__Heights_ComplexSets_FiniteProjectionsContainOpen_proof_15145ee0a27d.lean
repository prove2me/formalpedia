-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_FiniteProjectionsContainOpen_proof_15145ee0a27d
-- name    : P2M_GroundTheory_Heights__Heights_ComplexSets_FiniteProjectionsContainOpen_proof_15145ee0a27d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:45:21.577802+00:00
-- url     : https://prove2.me/theorems/f6e41401-c7cb-4559-8926-548a1ed93eeb
-- title:
--   P2 M Ground Theory Heights  Heights Complex Sets Finite Projections Contain Open proof 15145ee0a27d: P2 M Ground Theory Heights  Heights Complex Sets Finite Projections Contain Open proof 15145ee0a27d
-- statement:
--   The P2 M Ground Theory Heights  Heights Complex Sets Finite Projections Contain Open proof 15145ee0a27d construction uses the P2 M Ground Theory Heights  Heights Complex Sets Finite Projections Contain Open proof 15145ee0a27d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFiniteProjectionsContainOpen.lean#L15-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFiniteProjectionsContainOpen.lean#L15-L22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsConeAvoid
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteProjectionsGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StConeAvoidsFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteProjHomInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StConeAvoidsOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StConeAvoidsExists
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionsContainOpen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_ComplexSets_FiniteProjectionsContainOpen_proof_15145ee0a27d (h₁ : ConeAvoidsFinite.Statement)
    (h₂ : FiniteProjHomInjective.Statement) (h₃ : ConeAvoidsOpen.Statement)
    (h₄ : ConeAvoidsExists.Statement) : FiniteProjectionsContainOpen.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ComplexSets».«FiniteProjectionsContainOpen».«proof» := P2M_GroundTheory_Heights__Heights_ComplexSets_FiniteProjectionsContainOpen_proof_15145ee0a27d
