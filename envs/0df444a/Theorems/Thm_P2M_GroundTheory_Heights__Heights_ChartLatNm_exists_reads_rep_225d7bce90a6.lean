-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartLatNm_exists_reads_rep_225d7bce90a6
-- name    : P2M_GroundTheory_Heights__Heights_ChartLatNm_exists_reads_rep_225d7bce90a6
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:57:14.102848+00:00
-- url     : https://prove2.me/theorems/02647dc0-91fc-46a4-947b-d1a2bc317b91
-- title:
--   P2 M Ground Theory Heights  Heights Chart Lat Nm exists reads rep 225d7bce90a6: P2 M Ground Theory Heights  Heights Chart Lat Nm exists reads rep 225d7bce90a6
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Lat Nm exists reads rep 225d7bce90a6 construction uses the P2 M Ground Theory Heights  Heights Chart Lat Nm exists reads rep 225d7bce90a6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PChartLatNmSection.lean#L146-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PChartLatNmSection.lean#L146-L170

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

theorem P2M_GroundTheory_Heights__Heights_ChartLatNm_exists_reads_rep_225d7bce90a6 (hb : Geo.Birational (ι := blockIdx n) y) (c₀ : (k : ι) → Fin (n k + 1))
    (hc₀ : ∀ k, y ⟨k, c₀ k⟩ ≠ 0) (b : ι → ℤ) (s : Ω) :
    ∃ (f q : MvPolynomial (Coord n) ℤ) (δf δq : ι → ℕ), IsWeightedHomogeneous (coordDeg n) f δf ∧
      IsWeightedHomogeneous (coordDeg n) q δq ∧ (∀ k, (δf k : ℤ) = δq k + b k) ∧ aeval y q ≠ 0 ∧
      aeval y f = s * aeval y q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartLatNm».«exists_reads_rep» := P2M_GroundTheory_Heights__Heights_ChartLatNm_exists_reads_rep_225d7bce90a6
