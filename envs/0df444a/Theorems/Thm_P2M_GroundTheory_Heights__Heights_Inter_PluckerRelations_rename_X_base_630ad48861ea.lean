-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PluckerRelations_rename_X_base_630ad48861ea
-- name    : P2M_GroundTheory_Heights__Heights_Inter_PluckerRelations_rename_X_base_630ad48861ea
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:12:32.103786+00:00
-- url     : https://prove2.me/theorems/0b055f20-c3fc-4ed1-93f5-a219cd85b6c8
-- title:
--   P2 M Ground Theory Heights  Heights Inter Plucker Relations rename X base 630ad48861ea: P2 M Ground Theory Heights  Heights Inter Plucker Relations rename X base 630ad48861ea
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Plucker Relations rename X base 630ad48861ea construction uses the P2 M Ground Theory Heights  Heights Inter Plucker Relations rename X base 630ad48861ea property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PPluckerRel.lean#L92-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PPluckerRel.lean#L92-L94

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

theorem P2M_GroundTheory_Heights__Heights_Inter_PluckerRelations_rename_X_base_630ad48861ea (j : S.ι) :
    (rename (T.yyEmb 0) (X ⟨T.YBlk.base, j⟩ : MRing S.YIdx) : MRing S.WIdx) = X ⟨T.WBlk.base, j⟩ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«PluckerRelations».«rename_X_base» := P2M_GroundTheory_Heights__Heights_Inter_PluckerRelations_rename_X_base_630ad48861ea
