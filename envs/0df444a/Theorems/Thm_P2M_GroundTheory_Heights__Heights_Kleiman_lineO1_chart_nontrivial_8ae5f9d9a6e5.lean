-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_lineO1_chart_nontrivial_8ae5f9d9a6e5
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_lineO1_chart_nontrivial_8ae5f9d9a6e5
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:27:53.724085+00:00
-- url     : https://prove2.me/theorems/e2d4f68d-8446-45ce-bac6-725b949c7297
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman line O1 chart nontrivial 8ae5f9d9a6e5: P2 M Ground Theory Heights  Heights Kleiman line O1 chart nontrivial 8ae5f9d9a6e5
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman line O1 chart nontrivial 8ae5f9d9a6e5 construction uses the P2 M Ground Theory Heights  Heights Kleiman line O1 chart nontrivial 8ae5f9d9a6e5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/Objects.lean#L937-L942
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/Objects.lean#L937-L942

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_lineO1_chart_nontrivial_8ae5f9d9a6e5 : Nontrivial ((tautologicalLineBundle k).toSubFamily.toFamily.F (lineChart0 k)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«lineO1_chart_nontrivial» := P2M_GroundTheory_Heights__Heights_Kleiman_lineO1_chart_nontrivial_8ae5f9d9a6e5
