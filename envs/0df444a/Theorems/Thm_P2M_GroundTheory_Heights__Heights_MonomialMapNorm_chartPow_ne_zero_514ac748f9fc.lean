-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MonomialMapNorm_chartPow_ne_zero_514ac748f9fc
-- name    : P2M_GroundTheory_Heights__Heights_MonomialMapNorm_chartPow_ne_zero_514ac748f9fc
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:50:21.089905+00:00
-- url     : https://prove2.me/theorems/09db2135-fb4b-4afc-858c-60f7db9f1480
-- title:
--   P2 M Ground Theory Heights  Heights Monomial Map Norm chart Pow ne zero 514ac748f9fc: P2 M Ground Theory Heights  Heights Monomial Map Norm chart Pow ne zero 514ac748f9fc
-- statement:
--   The P2 M Ground Theory Heights  Heights Monomial Map Norm chart Pow ne zero 514ac748f9fc construction uses the P2 M Ground Theory Heights  Heights Monomial Map Norm chart Pow ne zero 514ac748f9fc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroBis.lean#L44-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroBis.lean#L44-L46

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZeroBis
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
open GroundTheory.Heights₂.Heights.MonomialMapNorm
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable (P : ArithVariety n)

theorem P2M_GroundTheory_Heights__Heights_MonomialMapNorm_chartPow_ne_zero_514ac748f9fc {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c) (a : ι → ℤ) :
    P.chartPow c a ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MonomialMapNorm».«chartPow_ne_zero» := P2M_GroundTheory_Heights__Heights_MonomialMapNorm_chartPow_ne_zero_514ac748f9fc
