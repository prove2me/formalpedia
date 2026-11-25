-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_chartMap_eq_zero_8731551ff692
-- name    : P2M_GroundTheory_Heights__Heights_ArithVariety_chartMap_eq_zero_8731551ff692
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:15:14.672802+00:00
-- url     : https://prove2.me/theorems/2185bb56-a864-4706-a989-3429ab6abad9
-- title:
--   P2 M Ground Theory Heights  Heights Arith Variety chart Map eq zero 8731551ff692: P2 M Ground Theory Heights  Heights Arith Variety chart Map eq zero 8731551ff692
-- statement:
--   The P2 M Ground Theory Heights  Heights Arith Variety chart Map eq zero 8731551ff692 construction uses the P2 M Ground Theory Heights  Heights Arith Variety chart Map eq zero 8731551ff692 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/DenseChart.lean#L128-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/DenseChart.lean#L128-L143

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

theorem P2M_GroundTheory_Heights__Heights_ArithVariety_chartMap_eq_zero_8731551ff692 (hc : ∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ P.ideal)
    {f : MvPolynomial (Coord n) ℤ} (hf : f ∈ P.ideal) :
    P.chartMap c (map (Int.castRingHom ℚ) f) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ArithVariety».«chartMap_eq_zero» := P2M_GroundTheory_Heights__Heights_ArithVariety_chartMap_eq_zero_8731551ff692
