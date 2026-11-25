-- Prove2me | Theorems.Thm_P2M_GroundTheory_Automorphic_ContragredientTranspose_transposeGL_smul__830060f4e8c6
-- name    : P2M_GroundTheory_Automorphic_ContragredientTranspose_transposeGL_smul__830060f4e8c6
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T01:36:31.00667+00:00
-- url     : https://prove2.me/theorems/0f3467ac-e290-48aa-b0a3-11fc0efa913c
-- title:
--   P2 M Ground Theory Automorphic Contragredient Transpose transpose GL smul  830060f4e8c6: P2 M Ground Theory Automorphic Contragredient Transpose transpose GL smul  830060f4e8c6
-- statement:
--   The P2 M Ground Theory Automorphic Contragredient Transpose transpose GL smul  830060f4e8c6 construction uses the P2 M Ground Theory Automorphic Contragredient Transpose transpose GL smul  830060f4e8c6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/GelfandKazhdan.lean#L380-L382
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/GelfandKazhdan.lean#L380-L382

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerOrbit
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerDistribution
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_MatrixSimilarity
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_GelfandKazhdan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.ContragredientTranspose
open Set Filter Topology MulAction Matrix GroundTheory.Automorphic.Whittaker
variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F] {n : ℕ}
omit [TopologicalSpace F] [IsTopologicalRing F]

theorem P2M_GroundTheory_Automorphic_ContragredientTranspose_transposeGL_smul__830060f4e8c6 (h : ConjAct (GL (Fin n) F)) (x : GL (Fin n) F) :
    transposeGL (h • x) = thetaC h • transposeGL x := by sorry

alias «GroundTheory».«Automorphic».«ContragredientTranspose».«transposeGL_smul'» := P2M_GroundTheory_Automorphic_ContragredientTranspose_transposeGL_smul__830060f4e8c6
