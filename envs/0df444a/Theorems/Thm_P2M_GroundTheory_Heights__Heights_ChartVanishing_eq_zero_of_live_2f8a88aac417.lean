-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartVanishing_eq_zero_of_live_2f8a88aac417
-- name    : P2M_GroundTheory_Heights__Heights_ChartVanishing_eq_zero_of_live_2f8a88aac417
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:57:46.183248+00:00
-- url     : https://prove2.me/theorems/edbc3873-8346-5123-98e3-53a6e6cf875b
-- title:
--   P2 M Ground Theory Heights  Heights Chart Vanishing eq zero of live 2f8a88aac417: P2 M Ground Theory Heights  Heights Chart Vanishing eq zero of live 2f8a88aac417
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Vanishing eq zero of live 2f8a88aac417 construction uses the P2 M Ground Theory Heights  Heights Chart Vanishing eq zero of live 2f8a88aac417 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroTer.lean#L134-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroTer.lean#L134-L147

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

theorem P2M_GroundTheory_Heights__Heights_ChartVanishing_eq_zero_of_live_2f8a88aac417 {P : ArithVariety n} {D : AddBlockData P} {d : ι → ℕ}
    {g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ}
    (hg : D.IsFormSystem d g) {z : Cone n ℂ} (hz : z ∈ P.points ℂ) {c : (k : ι) → Fin (n k + 1)}
    (hc : P.IsLive c) (hm : evalCone z (chartMonomial c d) = 0) (j : Fin (D.size + 1)) :
    evalCone z (g c j) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartVanishing».«eq_zero_of_live» := P2M_GroundTheory_Heights__Heights_ChartVanishing_eq_zero_of_live_2f8a88aac417
