-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartLatNm_isOfDegree_readElt_1d0629766c62
-- name    : P2M_GroundTheory_Heights__Heights_ChartLatNm_isOfDegree_readElt_1d0629766c62
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:16:14.063387+00:00
-- url     : https://prove2.me/theorems/d44a6658-3438-4673-9c67-929a6a4798eb
-- title:
--   P2 M Ground Theory Heights  Heights Chart Lat Nm is Of Degree read Elt 1d0629766c62: P2 M Ground Theory Heights  Heights Chart Lat Nm is Of Degree read Elt 1d0629766c62
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Lat Nm is Of Degree read Elt 1d0629766c62 construction uses the P2 M Ground Theory Heights  Heights Chart Lat Nm is Of Degree read Elt 1d0629766c62 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PChartLatNmSection.lean#L319-L327
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PChartLatNmSection.lean#L319-L327

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PChartLatNmSection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.ChartLatNm
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {Ω : Type} [Field Ω]
variable (P : ArithVariety n) (y : Coord n → Ω)
variable (hP : P.ideal = Geo.mCoordIdeal (ι := blockIdx n) y) (hb : Geo.Birational (ι := blockIdx n) y)

theorem P2M_GroundTheory_Heights__Heights_ChartLatNm_isOfDegree_readElt_1d0629766c62 (c₀ : (k : ι) → Fin (n k + 1)) (hc₀ : ∀ k, y ⟨k, c₀ k⟩ ≠ 0) (b : ι → ℤ)
    (s : Ω) : P.IsOfDegree b (readElt P y hP hb c₀ b s) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartLatNm».«isOfDegree_readElt» := P2M_GroundTheory_Heights__Heights_ChartLatNm_isOfDegree_readElt_1d0629766c62
