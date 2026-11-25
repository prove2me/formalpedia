-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_chartPoint_mem_ca013b7a7355
-- name    : P2M_GroundTheory_Heights__Heights_ArithVariety_chartPoint_mem_ca013b7a7355
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:07:28.239538+00:00
-- url     : https://prove2.me/theorems/0fa8e7d5-155f-539d-bdf3-8d1901485d68
-- title:
--   P2 M Ground Theory Heights  Heights Arith Variety chart Point mem ca013b7a7355: P2 M Ground Theory Heights  Heights Arith Variety chart Point mem ca013b7a7355
-- statement:
--   The P2 M Ground Theory Heights  Heights Arith Variety chart Point mem ca013b7a7355 construction uses the P2 M Ground Theory Heights  Heights Arith Variety chart Point mem ca013b7a7355 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/DenseChart.lean#L145-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/DenseChart.lean#L145-L161

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
variable (c : (k : ι) → Fin (n k + 1))

theorem P2M_GroundTheory_Heights__Heights_ArithVariety_chartPoint_mem_ca013b7a7355 (hc : ∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ P.ideal)
    (ψ : P.ChartAlg c →ₐ[ℚ] AlgebraicClosure ℚ) :
    P.chartPoint c ψ ∈ P.points (AlgebraicClosure ℚ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ArithVariety».«chartPoint_mem» := P2M_GroundTheory_Heights__Heights_ArithVariety_chartPoint_mem_ca013b7a7355
