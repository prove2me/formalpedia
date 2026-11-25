-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SemilocRankFrac_aeval_scale_73809ecd743e
-- name    : P2M_GroundTheory_Heights__Heights_Inter_SemilocRankFrac_aeval_scale_73809ecd743e
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:48:33.890396+00:00
-- url     : https://prove2.me/theorems/ce470f1b-30f5-59aa-8d01-127715afc171
-- title:
--   P2 M Ground Theory Heights  Heights Inter Semiloc Rank Frac aeval scale 73809ecd743e: P2 M Ground Theory Heights  Heights Inter Semiloc Rank Frac aeval scale 73809ecd743e
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Semiloc Rank Frac aeval scale 73809ecd743e construction uses the P2 M Ground Theory Heights  Heights Inter Semiloc Rank Frac aeval scale 73809ecd743e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSemilocRankFrac.lean#L23-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSemilocRankFrac.lean#L23-L37

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StSemilocRankFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StRankFracDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StSemilocChartRatio
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemilocRankFrac
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
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.Inter.SemilocRankFrac
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem P2M_GroundTheory_Heights__Heights_Inter_SemilocRankFrac_aeval_scale_73809ecd743e (y : (Σ k, ι k) → Ω) (c : K → Ω) {u : MRing ι} {a : K → ℕ} (hu : IsMultiHomog u a) :
    aeval (fun p => y p * c p.1) u = aeval y u * ∏ k, c k ^ a k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«SemilocRankFrac».«aeval_scale» := P2M_GroundTheory_Heights__Heights_Inter_SemilocRankFrac_aeval_scale_73809ecd743e
