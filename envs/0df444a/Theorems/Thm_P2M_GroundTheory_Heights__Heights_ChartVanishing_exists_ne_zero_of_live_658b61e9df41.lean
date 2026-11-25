-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartVanishing_exists_ne_zero_of_live_658b61e9df41
-- name    : P2M_GroundTheory_Heights__Heights_ChartVanishing_exists_ne_zero_of_live_658b61e9df41
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:17:53.290265+00:00
-- url     : https://prove2.me/theorems/a67da71b-edfa-446e-adfb-a83d84e58bdc
-- title:
--   P2 M Ground Theory Heights  Heights Chart Vanishing exists ne zero of live 658b61e9df41: P2 M Ground Theory Heights  Heights Chart Vanishing exists ne zero of live 658b61e9df41
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Vanishing exists ne zero of live 658b61e9df41 construction uses the P2 M Ground Theory Heights  Heights Chart Vanishing exists ne zero of live 658b61e9df41 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroTer.lean#L101-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroTer.lean#L101-L132

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZeroTer
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
open GroundTheory.Heights₂.Heights.ChartVanishing
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChartVanishing_exists_ne_zero_of_live_658b61e9df41 {P : ArithVariety n} {D : AddBlockData P} {d : ι → ℕ}
    {g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ}
    (hg : D.IsFormSystem d g) {z : Cone n ℂ} (hz : z ∈ P.points ℂ) {c : (k : ι) → Fin (n k + 1)}
    (hc : P.IsLive c) (hm : evalCone z (chartMonomial c d) ≠ 0) : ∃ j, evalCone z (g c j) ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartVanishing».«exists_ne_zero_of_live» := P2M_GroundTheory_Heights__Heights_ChartVanishing_exists_ne_zero_of_live_658b61e9df41
