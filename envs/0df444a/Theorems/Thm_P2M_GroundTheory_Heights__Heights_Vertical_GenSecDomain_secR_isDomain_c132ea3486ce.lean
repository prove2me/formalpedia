-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_GenSecDomain_secR_isDomain_c132ea3486ce
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_GenSecDomain_secR_isDomain_c132ea3486ce
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:42:53.48661+00:00
-- url     : https://prove2.me/theorems/24aeeae1-a7d6-45ff-bc6b-979640602ef5
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Gen Sec Domain sec R is Domain c132ea3486ce: P2 M Ground Theory Heights  Heights Vertical Gen Sec Domain sec R is Domain c132ea3486ce
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Gen Sec Domain sec R is Domain c132ea3486ce construction uses the P2 M Ground Theory Heights  Heights Vertical Gen Sec Domain sec R is Domain c132ea3486ce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PGenSecDomain.lean#L193-L258
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PGenSecDomain.lean#L193-L258

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

theorem P2M_GroundTheory_Heights__Heights_Vertical_GenSecDomain_secR_isDomain_c132ea3486ce (h₁ : ChartDomain.Statement) (Q : Ideal (MvPolynomial (Fin n) k)) (e : ℕ)
    (hQ : IsProjPrime Q) {Ω : Type} [Field Ω] (Ψ : SecR Q e →+* Ω)
    (hΨ : ∀ l, X l ∉ Q → Ψ (xc Q e l) ≠ 0) : IsDomain (SecR Q e) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«GenSecDomain».«secR_isDomain» := P2M_GroundTheory_Heights__Heights_Vertical_GenSecDomain_secR_isDomain_c132ea3486ce
