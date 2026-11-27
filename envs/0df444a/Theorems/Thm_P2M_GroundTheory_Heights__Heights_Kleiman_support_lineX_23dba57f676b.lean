-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_support_lineX_23dba57f676b
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_support_lineX_23dba57f676b
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:28:16.295609+00:00
-- url     : https://prove2.me/theorems/79123b12-c8c7-481e-abea-daf0b3112428
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman support line X 23dba57f676b: P2 M Ground Theory Heights  Heights Kleiman support line X 23dba57f676b
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman support line X 23dba57f676b construction uses the P2 M Ground Theory Heights  Heights Kleiman support line X 23dba57f676b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/Objects.lean#L925-L927
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/Objects.lean#L925-L927

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
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
universe u v w
variable (k : Type u) [Field k]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_support_lineX_23dba57f676b : support (lineX k) = Finset.univ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«support_lineX» := P2M_GroundTheory_Heights__Heights_Kleiman_support_lineX_23dba57f676b
