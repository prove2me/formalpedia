-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_exists_chart_5599c818fd08
-- name    : P2M_GroundTheory_Heights__Heights_ArithVariety_exists_chart_5599c818fd08
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:43:57.164698+00:00
-- url     : https://prove2.me/theorems/ea6f435a-5c45-4012-ba85-4b721200b620
-- title:
--   P2 M Ground Theory Heights  Heights Arith Variety exists chart 5599c818fd08: P2 M Ground Theory Heights  Heights Arith Variety exists chart 5599c818fd08
-- statement:
--   The P2 M Ground Theory Heights  Heights Arith Variety exists chart 5599c818fd08 construction uses the P2 M Ground Theory Heights  Heights Arith Variety exists chart 5599c818fd08 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/DenseChart.lean#L54-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/DenseChart.lean#L54-L56

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_DenseChart
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
open MvPolynomial
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
open GroundTheory.Heights₂.Heights.ArithVariety
variable (P : ArithVariety n)
omit [Fintype ι]

theorem P2M_GroundTheory_Heights__Heights_ArithVariety_exists_chart_5599c818fd08 :
    ∃ c : (k : ι) → Fin (n k + 1), ∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ P.ideal := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ArithVariety».«exists_chart» := P2M_GroundTheory_Heights__Heights_ArithVariety_exists_chart_5599c818fd08
