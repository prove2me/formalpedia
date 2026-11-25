-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MonomialMapNorm_chartForm_bound_86ac715e5797
-- name    : P2M_GroundTheory_Heights__Heights_MonomialMapNorm_chartForm_bound_86ac715e5797
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:52:53.638324+00:00
-- url     : https://prove2.me/theorems/122c489f-48aa-5c4e-bfee-2d47df478551
-- title:
--   P2 M Ground Theory Heights  Heights Monomial Map Norm chart Form bound 86ac715e5797: P2 M Ground Theory Heights  Heights Monomial Map Norm chart Form bound 86ac715e5797
-- statement:
--   The P2 M Ground Theory Heights  Heights Monomial Map Norm chart Form bound 86ac715e5797 construction uses the P2 M Ground Theory Heights  Heights Monomial Map Norm chart Form bound 86ac715e5797 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroBis.lean#L115-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroBis.lean#L115-L121

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

theorem P2M_GroundTheory_Heights__Heights_MonomialMapNorm_chartForm_bound_86ac715e5797 {A : HermLine n} {s : IntegralSection P A.deg} (hs : s.SupNormLE A 0)
    {z : Cone n ℂ} (hz : z ∈ P.points ℂ) {c : (k : ι) → Fin (n k + 1)} {d : ι → ℕ}
    {e : MvPolynomial (Coord n) ℤ} (he : IsChartForm P A.deg s.num s.den c d e) (hcz : ∀ k, z k (c k) ≠ 0) :
    ‖evalCone z e‖ ≤ ‖evalCone z (chartMonomial c d)‖ * A.metric z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MonomialMapNorm».«chartForm_bound» := P2M_GroundTheory_Heights__Heights_MonomialMapNorm_chartForm_bound_86ac715e5797
