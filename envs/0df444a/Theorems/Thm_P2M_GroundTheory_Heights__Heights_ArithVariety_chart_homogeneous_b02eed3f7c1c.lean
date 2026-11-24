-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_chart_homogeneous_b02eed3f7c1c
-- name    : P2M_GroundTheory_Heights__Heights_ArithVariety_chart_homogeneous_b02eed3f7c1c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:45:09.961593+00:00
-- url     : https://prove2.me/theorems/9321c4e2-e5a6-4a30-a1c2-c36c02a3b8e3
-- title:
--   P2 M Ground Theory Heights  Heights Arith Variety chart homogeneous b02eed3f7c1c: P2 M Ground Theory Heights  Heights Arith Variety chart homogeneous b02eed3f7c1c
-- statement:
--   The P2 M Ground Theory Heights  Heights Arith Variety chart homogeneous b02eed3f7c1c construction uses the P2 M Ground Theory Heights  Heights Arith Variety chart homogeneous b02eed3f7c1c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/DenseChart.lean#L100-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/DenseChart.lean#L100-L112

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

theorem P2M_GroundTheory_Heights__Heights_ArithVariety_chart_homogeneous_b02eed3f7c1c (hc : ∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ P.ideal)
    {f : MvPolynomial (Coord n) ℤ} {δ : ι → ℕ} (hf : IsWeightedHomogeneous (coordDeg n) f δ) :
    (∏ k, P.mkF (X ⟨k, c k⟩) ^ δ k) * eval₂ (Int.castRingHom _) (P.chartCoord c) f = P.mkF f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ArithVariety».«chart_homogeneous» := P2M_GroundTheory_Heights__Heights_ArithVariety_chart_homogeneous_b02eed3f7c1c
