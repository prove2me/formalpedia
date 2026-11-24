-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SerreVanish_proof_0500a1a6c152
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SerreVanish_proof_0500a1a6c152
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:33:12.60431+00:00
-- url     : https://prove2.me/theorems/34e3658a-72c9-4047-965f-dcd149fa3d80
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Serre Vanish proof 0500a1a6c152: P2 M Ground Theory Heights  Heights Kleiman Serre Vanish proof 0500a1a6c152
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Serre Vanish proof 0500a1a6c152 construction uses the P2 M Ground Theory Heights  Heights Kleiman Serre Vanish proof 0500a1a6c152 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerreVanish.lean#L14-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerreVanish.lean#L14-L52

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsPres
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerreVanish
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
open MvPolynomial
noncomputable section
universe u v

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SerreVanish_proof_0500a1a6c152 (hExact : CechExact.Statement.{u, max u v})
    (hTop : CechTop.Statement.{u, max u v}) (hFree : SerreFree.Statement.{u, max u v})
    (hPres : GradedPres.Statement.{u, v}) (hLift : GradedULift.Statement.{u, v})
    (hRet : CohomRetract.Statement.{u, v, max u v}) : SerreVanish.Statement.{u, v} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SerreVanish».«proof» := P2M_GroundTheory_Heights__Heights_Kleiman_SerreVanish_proof_0500a1a6c152
