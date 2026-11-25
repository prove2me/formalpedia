-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PluckerRelations_chart_form_82dccfe371dc
-- name    : P2M_GroundTheory_Heights__Heights_Inter_PluckerRelations_chart_form_82dccfe371dc
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:23:28.859297+00:00
-- url     : https://prove2.me/theorems/0914c2e3-0e6f-430e-9fe9-c9ee108027ae
-- title:
--   P2 M Ground Theory Heights  Heights Inter Plucker Relations chart form 82dccfe371dc: P2 M Ground Theory Heights  Heights Inter Plucker Relations chart form 82dccfe371dc
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Plucker Relations chart form 82dccfe371dc construction uses the P2 M Ground Theory Heights  Heights Inter Plucker Relations chart form 82dccfe371dc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PPluckerRel.lean#L96-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PPluckerRel.lean#L96-L145

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_XiPluckerRel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PPluckerRel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.PluckerRelations
variable {D : ℕ} (S : ProjectiveLineBundle D)

theorem P2M_GroundTheory_Heights__Heights_Inter_PluckerRelations_chart_form_82dccfe371dc (i : S.ι) (hi : S.x i ≠ 0) {a : S.Ω} (ha : a ∈ chartRing ℤ S.x i) :
    ∃ (d : ℕ) (Q : MRing S.YIdx), IsMultiHomog Q (Pi.single T.YBlk.base d) ∧
      IsMultiHomog (rename (T.yyEmb 0) Q : MRing S.WIdx) (Pi.single T.WBlk.base d) ∧
      aeval (T.wwCoord S.x S.δ S.e S.φ (S.a 0) (S.a 1)) (rename (T.yyEmb 0) Q) =
        algebraMap S.Ω S.Φ (S.x i ^ d * a) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«PluckerRelations».«chart_form» := P2M_GroundTheory_Heights__Heights_Inter_PluckerRelations_chart_form_82dccfe371dc
