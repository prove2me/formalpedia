-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_chartMap_map_94d14512901d
-- name    : P2M_GroundTheory_Heights__Heights_ArithVariety_chartMap_map_94d14512901d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:49:12.505968+00:00
-- url     : https://prove2.me/theorems/76faf83a-a34f-43b7-b24c-4a8757604034
-- title:
--   P2 M Ground Theory Heights  Heights Arith Variety chart Map map 94d14512901d: P2 M Ground Theory Heights  Heights Arith Variety chart Map map 94d14512901d
-- statement:
--   The P2 M Ground Theory Heights  Heights Arith Variety chart Map map 94d14512901d construction uses the P2 M Ground Theory Heights  Heights Arith Variety chart Map map 94d14512901d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/DenseChart.lean#L94-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/DenseChart.lean#L94-L98

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
omit [Fintype ι]

theorem P2M_GroundTheory_Heights__Heights_ArithVariety_chartMap_map_94d14512901d (f : MvPolynomial (Coord n) ℤ) :
    P.chartMap c (map (Int.castRingHom ℚ) f) = eval₂ (Int.castRingHom _) (P.chartCoord c) f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ArithVariety».«chartMap_map» := P2M_GroundTheory_Heights__Heights_ArithVariety_chartMap_map_94d14512901d
