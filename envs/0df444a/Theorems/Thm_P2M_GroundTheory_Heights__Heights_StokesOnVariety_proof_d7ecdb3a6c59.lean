-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StokesOnVariety_proof_d7ecdb3a6c59
-- name    : P2M_GroundTheory_Heights__Heights_StokesOnVariety_proof_d7ecdb3a6c59
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:38:18.330824+00:00
-- url     : https://prove2.me/theorems/f00ceb9a-e68e-4267-8ba4-af333b568e2e
-- title:
--   P2 M Ground Theory Heights  Heights Stokes On Variety proof d7ecdb3a6c59: P2 M Ground Theory Heights  Heights Stokes On Variety proof d7ecdb3a6c59
-- statement:
--   The P2 M Ground Theory Heights  Heights Stokes On Variety proof d7ecdb3a6c59 construction uses the P2 M Ground Theory Heights  Heights Stokes On Variety proof d7ecdb3a6c59 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PStokesOnVariety.lean#L12-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PStokesOnVariety.lean#L12-L51

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StStokesOffDiscriminant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffLimit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PStokesOnVariety
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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

theorem P2M_GroundTheory_Heights__Heights_StokesOnVariety_proof_d7ecdb3a6c59 (hD : ComplexSets.DiscriminantCover.Statement)
    (hS : StokesOffDiscriminant.Statement) (hL : CutOffLimit.Statement) :
    StokesOnVariety.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StokesOnVariety».«proof» := P2M_GroundTheory_Heights__Heights_StokesOnVariety_proof_d7ecdb3a6c59
