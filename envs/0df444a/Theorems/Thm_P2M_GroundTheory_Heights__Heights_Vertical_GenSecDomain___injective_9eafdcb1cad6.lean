-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_GenSecDomain___injective_9eafdcb1cad6
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_GenSecDomain___injective_9eafdcb1cad6
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:42:24.026257+00:00
-- url     : https://prove2.me/theorems/0b4473af-e4d1-4120-bcce-76739244d3be
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Gen Sec Domain   injective 9eafdcb1cad6: P2 M Ground Theory Heights  Heights Vertical Gen Sec Domain   injective 9eafdcb1cad6
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Gen Sec Domain   injective 9eafdcb1cad6 construction uses the P2 M Ground Theory Heights  Heights Vertical Gen Sec Domain   injective 9eafdcb1cad6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PGenSecDomain.lean#L74-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PGenSecDomain.lean#L74-L78

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_ComapMaximalIdealParDVR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PGenSecDomain
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
open GroundTheory.Heights₂.Heights.Vertical.GenSecDomain
variable {k : Type} [Field k] {n : ℕ}
variable (Q : Ideal (MvPolynomial (Fin n) k)) [Q.IsPrime] (e : ℕ)
omit [Q.IsPrime]

theorem P2M_GroundTheory_Heights__Heights_Vertical_GenSecDomain___injective_9eafdcb1cad6 (c : Fin n → Fn Q) (h : Function.Injective (gsub Q e c)) :
    Function.Injective (ρ Q e c) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«GenSecDomain».«ρ_injective» := P2M_GroundTheory_Heights__Heights_Vertical_GenSecDomain___injective_9eafdcb1cad6
