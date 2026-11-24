-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_Xpow_homog_6fdb90b2f59f
-- name    : P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_Xpow_homog_6fdb90b2f59f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:22:35.682905+00:00
-- url     : https://prove2.me/theorems/0c02dd48-c80b-45ff-b5fa-e08075c62109
-- title:
--   P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover Xpow homog 6fdb90b2f59f: P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover Xpow homog 6fdb90b2f59f
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover Xpow homog 6fdb90b2f59f construction uses the P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover Xpow homog 6fdb90b2f59f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PPluckerCover.lean#L236-L241
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PPluckerCover.lean#L236-L241

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_XiPluckerCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PPluckerCover
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
open GroundTheory.Heights₂.Heights.Inter.PluckerAffineCover
variable {D : ℕ} (S : ProjectiveLineBundle D)

theorem P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_Xpow_homog_6fdb90b2f59f (i : S.ι) (d : ℕ) :
    IsWeightedHomogeneous (wt S) (X ⟨.base, i⟩ ^ d : MRing S.YIdx) (Pi.single .base d) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«PluckerAffineCover».«Xpow_homog» := P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_Xpow_homog_6fdb90b2f59f
