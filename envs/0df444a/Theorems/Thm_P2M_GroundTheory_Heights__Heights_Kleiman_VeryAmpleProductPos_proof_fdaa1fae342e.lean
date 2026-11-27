-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleProductPos_proof_fdaa1fae342e
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleProductPos_proof_fdaa1fae342e
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:30:29.408481+00:00
-- url     : https://prove2.me/theorems/ad92c476-5785-5a68-8e94-5f81eff7d596
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Very Ample Product Pos proof fdaa1fae342e: P2 M Ground Theory Heights  Heights Kleiman Very Ample Product Pos proof fdaa1fae342e
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Very Ample Product Pos proof fdaa1fae342e construction uses the P2 M Ground Theory Heights  Heights Kleiman Very Ample Product Pos proof fdaa1fae342e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleProductPos.lean#L16-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleProductPos.lean#L16-L53

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleProductPosSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PointDegreePosSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CutComponentSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CutMultPosSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleProductPos
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
universe u w

theorem P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleProductPos_proof_fdaa1fae342e (hR : GenericPointSectionInput.Statement.{u, w}) (hP : PointDegreePos.Statement.{u, w})
    (hC : CutComponent.Statement.{u, w}) (hM : CutMultPos.Statement.{u}) :
    VeryAmpleProductPos.Statement.{u, w} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«VeryAmpleProductPos».«proof» := P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleProductPos_proof_fdaa1fae342e
