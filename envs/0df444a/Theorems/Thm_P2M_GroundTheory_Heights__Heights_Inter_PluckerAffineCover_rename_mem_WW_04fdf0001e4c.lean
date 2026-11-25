-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_rename_mem_WW_04fdf0001e4c
-- name    : P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_rename_mem_WW_04fdf0001e4c
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:30:32.760297+00:00
-- url     : https://prove2.me/theorems/f4b9f53e-89bd-5e92-bc66-2dd96346b506
-- title:
--   P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover rename mem WW 04fdf0001e4c: P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover rename mem WW 04fdf0001e4c
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover rename mem WW 04fdf0001e4c construction uses the P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover rename mem WW 04fdf0001e4c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PPluckerCover.lean#L333-L337
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PPluckerCover.lean#L333-L337

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

theorem P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_rename_mem_WW_04fdf0001e4c (r : MRing S.YIdx) (b : T.YBlk → ℕ) (hr : IsMultiHomog r b) (h0 : aeval (yyc S) r = 0) :
    rename (T.yyEmb 0) r ∈ S.WW := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«PluckerAffineCover».«rename_mem_WW» := P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_rename_mem_WW_04fdf0001e4c
