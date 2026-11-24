-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MonomialMapNorm_mkF_chartForm_c55ff95110ec
-- name    : P2M_GroundTheory_Heights__Heights_MonomialMapNorm_mkF_chartForm_c55ff95110ec
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:28:47.487814+00:00
-- url     : https://prove2.me/theorems/33f063e0-a8d4-4128-a645-32dbd455800e
-- title:
--   P2 M Ground Theory Heights  Heights Monomial Map Norm mk F chart Form c55ff95110ec: P2 M Ground Theory Heights  Heights Monomial Map Norm mk F chart Form c55ff95110ec
-- statement:
--   The P2 M Ground Theory Heights  Heights Monomial Map Norm mk F chart Form c55ff95110ec construction uses the P2 M Ground Theory Heights  Heights Monomial Map Norm mk F chart Form c55ff95110ec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroBis.lean#L65-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroBis.lean#L65-L72

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

theorem P2M_GroundTheory_Heights__Heights_MonomialMapNorm_mkF_chartForm_c55ff95110ec {a : ι → ℤ} (s : IntegralSection P a) {c : (k : ι) → Fin (n k + 1)} {d : ι → ℕ}
    {e : MvPolynomial (Coord n) ℤ} (he : IsChartForm P a s.num s.den c d e) :
    P.mkF e = s.toFun * P.mkF (chartMonomial c d) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MonomialMapNorm».«mkF_chartForm» := P2M_GroundTheory_Heights__Heights_MonomialMapNorm_mkF_chartForm_c55ff95110ec
