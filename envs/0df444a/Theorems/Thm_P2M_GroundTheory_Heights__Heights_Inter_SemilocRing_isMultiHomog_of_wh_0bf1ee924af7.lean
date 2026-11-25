-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SemilocRing_isMultiHomog_of_wh_0bf1ee924af7
-- name    : P2M_GroundTheory_Heights__Heights_Inter_SemilocRing_isMultiHomog_of_wh_0bf1ee924af7
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:28:19.424844+00:00
-- url     : https://prove2.me/theorems/3594cabb-0611-5fc6-88ef-e7d9d4edeb74
-- title:
--   P2 M Ground Theory Heights  Heights Inter Semiloc Ring is Multi Homog of wh 0bf1ee924af7: P2 M Ground Theory Heights  Heights Inter Semiloc Ring is Multi Homog of wh 0bf1ee924af7
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Semiloc Ring is Multi Homog of wh 0bf1ee924af7 construction uses the P2 M Ground Theory Heights  Heights Inter Semiloc Ring is Multi Homog of wh 0bf1ee924af7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsSemilocRing.lean#L152-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsSemilocRing.lean#L152-L160

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IdDeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LocRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter
open GroundTheory.Heights₂.Heights.Inter.SemilocRing
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
open Classical

theorem P2M_GroundTheory_Heights__Heights_Inter_SemilocRing_isMultiHomog_of_wh_0bf1ee924af7 {s : MRing ι} {a : K → ℕ} (h : IsWeightedHomogeneous (blkW (ι := ι)) s a) :
    IsMultiHomog s a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«SemilocRing».«isMultiHomog_of_wh» := P2M_GroundTheory_Heights__Heights_Inter_SemilocRing_isMultiHomog_of_wh_0bf1ee924af7
