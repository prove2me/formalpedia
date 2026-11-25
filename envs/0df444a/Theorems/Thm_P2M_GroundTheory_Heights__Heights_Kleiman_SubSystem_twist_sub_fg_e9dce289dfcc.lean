-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_twist_sub_fg_e9dce289dfcc
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_twist_sub_fg_e9dce289dfcc
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T07:59:43.948452+00:00
-- url     : https://prove2.me/theorems/c4c3016d-2e7a-480f-8cd7-0d7d29008cab
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sub System twist sub fg e9dce289dfcc: P2 M Ground Theory Heights  Heights Kleiman Sub System twist sub fg e9dce289dfcc
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sub System twist sub fg e9dce289dfcc construction uses the P2 M Ground Theory Heights  Heights Kleiman Sub System twist sub fg e9dce289dfcc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PSubFamilyTwistX.lean#L19-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PSubFamilyTwistX.lean#L19-L52

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SubFamilyTwistSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSubFamilyTwistPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PSubFamilyTwistX
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
noncomputable section
universe u v w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
omit [Module S E] [IsScalarTower S Ω E]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_twist_sub_fg_e9dce289dfcc (F : SubSystem S x E) (Q : SubSystem S x Ω) (I : Chart x)
    (hF : (F.sub I).FG) (hQ : (Q.sub I).FG) : ((F.twist Q).sub I).FG := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SubSystem».«twist_sub_fg» := P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_twist_sub_fg_e9dce289dfcc
