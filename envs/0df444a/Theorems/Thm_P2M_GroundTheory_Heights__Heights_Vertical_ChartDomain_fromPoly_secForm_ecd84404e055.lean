-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_ChartDomain_fromPoly_secForm_ecd84404e055
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_ChartDomain_fromPoly_secForm_ecd84404e055
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:43:00.566262+00:00
-- url     : https://prove2.me/theorems/82df865e-a51f-440a-a9f8-8e045970fef5
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Chart Domain from Poly sec Form ecd84404e055: P2 M Ground Theory Heights  Heights Vertical Chart Domain from Poly sec Form ecd84404e055
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Chart Domain from Poly sec Form ecd84404e055 construction uses the P2 M Ground Theory Heights  Heights Vertical Chart Domain from Poly sec Form ecd84404e055 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PChartDomain.lean#L124-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PChartDomain.lean#L124-L129

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_ComapMaximalIdealParDVR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PChartDomain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.ChartDomain
variable {D : Type} [CommRing D] {n e : ℕ} (Q : Ideal (MvPolynomial (Fin n) D)) (j : Fin n)

theorem P2M_GroundTheory_Heights__Heights_Vertical_ChartDomain_fromPoly_secForm_ecd84404e055 (i : Fin e) :
    fromPoly Q j e (∑ m, X (.inl (i, m)) * cx Q j e m) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«ChartDomain».«fromPoly_secForm» := P2M_GroundTheory_Heights__Heights_Vertical_ChartDomain_fromPoly_secForm_ecd84404e055
