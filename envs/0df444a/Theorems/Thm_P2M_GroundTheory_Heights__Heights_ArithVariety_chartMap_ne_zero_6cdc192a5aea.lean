-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_chartMap_ne_zero_6cdc192a5aea
-- name    : P2M_GroundTheory_Heights__Heights_ArithVariety_chartMap_ne_zero_6cdc192a5aea
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:07:37.807034+00:00
-- url     : https://prove2.me/theorems/e410ac7e-ab1e-4b77-93dc-5e9a8a6962a7
-- title:
--   P2 M Ground Theory Heights  Heights Arith Variety chart Map ne zero 6cdc192a5aea: P2 M Ground Theory Heights  Heights Arith Variety chart Map ne zero 6cdc192a5aea
-- statement:
--   The P2 M Ground Theory Heights  Heights Arith Variety chart Map ne zero 6cdc192a5aea construction uses the P2 M Ground Theory Heights  Heights Arith Variety chart Map ne zero 6cdc192a5aea property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/DenseChart.lean#L163-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/DenseChart.lean#L163-L171

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

theorem P2M_GroundTheory_Heights__Heights_ArithVariety_chartMap_ne_zero_6cdc192a5aea (hc : ∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ P.ideal)
    {f : MvPolynomial (Coord n) ℤ} {δ : ι → ℕ} (hf : IsWeightedHomogeneous (coordDeg n) f δ)
    (hfP : f ∉ P.ideal) : (P.chartMap c).rangeRestrict (map (Int.castRingHom ℚ) f) ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ArithVariety».«chartMap_ne_zero» := P2M_GroundTheory_Heights__Heights_ArithVariety_chartMap_ne_zero_6cdc192a5aea
