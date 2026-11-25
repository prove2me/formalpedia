-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_ChartDomain_fromPoly_chartForm_efb69df01e78
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_ChartDomain_fromPoly_chartForm_efb69df01e78
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:42:33.318659+00:00
-- url     : https://prove2.me/theorems/ee258820-3480-4c95-8262-d5fd1f346074
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Chart Domain from Poly chart Form efb69df01e78: P2 M Ground Theory Heights  Heights Vertical Chart Domain from Poly chart Form efb69df01e78
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Chart Domain from Poly chart Form efb69df01e78 construction uses the P2 M Ground Theory Heights  Heights Vertical Chart Domain from Poly chart Form efb69df01e78 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PChartDomain.lean#L131-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PChartDomain.lean#L131-L136

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

theorem P2M_GroundTheory_Heights__Heights_Vertical_ChartDomain_fromPoly_chartForm_efb69df01e78 :
    fromPoly Q j e (∑ m, X (.inr m) * cx Q j e m - 1) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«ChartDomain».«fromPoly_chartForm» := P2M_GroundTheory_Heights__Heights_Vertical_ChartDomain_fromPoly_chartForm_efb69df01e78
