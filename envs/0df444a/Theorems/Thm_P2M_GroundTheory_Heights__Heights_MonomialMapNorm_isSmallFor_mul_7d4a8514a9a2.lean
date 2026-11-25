-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MonomialMapNorm_isSmallFor_mul_7d4a8514a9a2
-- name    : P2M_GroundTheory_Heights__Heights_MonomialMapNorm_isSmallFor_mul_7d4a8514a9a2
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:49:46.298878+00:00
-- url     : https://prove2.me/theorems/70ce7ab1-722c-48eb-8756-8c5920d8fbf3
-- title:
--   P2 M Ground Theory Heights  Heights Monomial Map Norm is Small For mul 7d4a8514a9a2: P2 M Ground Theory Heights  Heights Monomial Map Norm is Small For mul 7d4a8514a9a2
-- statement:
--   The P2 M Ground Theory Heights  Heights Monomial Map Norm is Small For mul 7d4a8514a9a2 construction uses the P2 M Ground Theory Heights  Heights Monomial Map Norm is Small For mul 7d4a8514a9a2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroBis.lean#L123-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroBis.lean#L123-L180

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

theorem P2M_GroundTheory_Heights__Heights_MonomialMapNorm_isSmallFor_mul_7d4a8514a9a2 {L : HermLine n} {q m r : ℕ} (hrq : r < q) {g : IntegralSection P L.deg}
    {h : IntegralSection P (HermLine.standard n).deg} (hgs : g.SupNormLE L 0)
    (hhs : h.SupNormLE (HermLine.standard n) 0) {s : P.FunField} (hsS : P.IsSmallFor (L.pow (q * m + r)) s) :
    P.IsSmallFor (((L.pow q).mul (HermLine.standard n)).pow (m + 1))
      (s * g.toFun ^ (q - r) * h.toFun ^ (m + 1)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MonomialMapNorm».«isSmallFor_mul» := P2M_GroundTheory_Heights__Heights_MonomialMapNorm_isSmallFor_mul_7d4a8514a9a2
