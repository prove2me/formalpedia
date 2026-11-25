-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_GenSecDomain___C_7487438d7ef4
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_GenSecDomain___C_7487438d7ef4
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:42:23.335531+00:00
-- url     : https://prove2.me/theorems/208a345d-9336-41a2-a355-abeb54b5902f
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Gen Sec Domain   C 7487438d7ef4: P2 M Ground Theory Heights  Heights Vertical Gen Sec Domain   C 7487438d7ef4
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Gen Sec Domain   C 7487438d7ef4 construction uses the P2 M Ground Theory Heights  Heights Vertical Gen Sec Domain   C 7487438d7ef4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PGenSecDomain.lean#L70-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PGenSecDomain.lean#L70-L71

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

theorem P2M_GroundTheory_Heights__Heights_Vertical_GenSecDomain___C_7487438d7ef4 (c : Fin n → Fn Q) (a : k) : ρ Q e c (C a) = C (C (algebraMap k (Fn Q) a)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«GenSecDomain».«ρ_C» := P2M_GroundTheory_Heights__Heights_Vertical_GenSecDomain___C_7487438d7ef4
