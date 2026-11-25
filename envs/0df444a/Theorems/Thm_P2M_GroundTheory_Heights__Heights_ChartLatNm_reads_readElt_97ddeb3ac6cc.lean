-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartLatNm_reads_readElt_97ddeb3ac6cc
-- name    : P2M_GroundTheory_Heights__Heights_ChartLatNm_reads_readElt_97ddeb3ac6cc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:50:15.963837+00:00
-- url     : https://prove2.me/theorems/f77a79aa-f71b-43dd-9881-d7c1131e5212
-- title:
--   P2 M Ground Theory Heights  Heights Chart Lat Nm reads read Elt 97ddeb3ac6cc: P2 M Ground Theory Heights  Heights Chart Lat Nm reads read Elt 97ddeb3ac6cc
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Lat Nm reads read Elt 97ddeb3ac6cc construction uses the P2 M Ground Theory Heights  Heights Chart Lat Nm reads read Elt 97ddeb3ac6cc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PChartLatNmSection.lean#L279-L307
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PChartLatNmSection.lean#L279-L307

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

theorem P2M_GroundTheory_Heights__Heights_ChartLatNm_reads_readElt_97ddeb3ac6cc (c₀ : (k : ι) → Fin (n k + 1)) (hc₀ : ∀ k, y ⟨k, c₀ k⟩ ≠ 0) (b : ι → ℤ) (s : Ω) :
    P.Reads y b s (readElt P y hP hb c₀ b s) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartLatNm».«reads_readElt» := P2M_GroundTheory_Heights__Heights_ChartLatNm_reads_readElt_97ddeb3ac6cc
