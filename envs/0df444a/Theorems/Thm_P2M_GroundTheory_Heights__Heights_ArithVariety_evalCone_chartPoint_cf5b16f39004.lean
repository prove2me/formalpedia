-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_evalCone_chartPoint_cf5b16f39004
-- name    : P2M_GroundTheory_Heights__Heights_ArithVariety_evalCone_chartPoint_cf5b16f39004
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:16:12.929837+00:00
-- url     : https://prove2.me/theorems/32fa98b7-9918-44e3-ad68-5601e1a26575
-- title:
--   P2 M Ground Theory Heights  Heights Arith Variety eval Cone chart Point cf5b16f39004: P2 M Ground Theory Heights  Heights Arith Variety eval Cone chart Point cf5b16f39004
-- statement:
--   The P2 M Ground Theory Heights  Heights Arith Variety eval Cone chart Point cf5b16f39004 construction uses the P2 M Ground Theory Heights  Heights Arith Variety eval Cone chart Point cf5b16f39004 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/DenseChart.lean#L119-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/DenseChart.lean#L119-L126

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

theorem P2M_GroundTheory_Heights__Heights_ArithVariety_evalCone_chartPoint_cf5b16f39004 (ψ : P.ChartAlg c →ₐ[ℚ] AlgebraicClosure ℚ)
    (f : MvPolynomial (Coord n) ℤ) :
    evalCone (P.chartPoint c ψ) f =
      ψ ((P.chartMap c).rangeRestrict (map (Int.castRingHom ℚ) f)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ArithVariety».«evalCone_chartPoint» := P2M_GroundTheory_Heights__Heights_ArithVariety_evalCone_chartPoint_cf5b16f39004
