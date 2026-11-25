-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_GenSecDomain_secIdeal_le_ker_859e8674bf60
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_GenSecDomain_secIdeal_le_ker_859e8674bf60
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:43:06.295216+00:00
-- url     : https://prove2.me/theorems/c89fb3a7-5f47-5e1d-81e5-94f8f08ba208
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Gen Sec Domain sec Ideal le ker 859e8674bf60: P2 M Ground Theory Heights  Heights Vertical Gen Sec Domain sec Ideal le ker 859e8674bf60
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Gen Sec Domain sec Ideal le ker 859e8674bf60 construction uses the P2 M Ground Theory Heights  Heights Vertical Gen Sec Domain sec Ideal le ker 859e8674bf60 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PGenSecDomain.lean#L107-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PGenSecDomain.lean#L107-L152

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

theorem P2M_GroundTheory_Heights__Heights_Vertical_GenSecDomain_secIdeal_le_ker_859e8674bf60 (hQh : IsHomogIdeal Q) (c : Fin n → Fn Q) (hc : ∑ j, c j * genPt Q j = 1)
    (hs : sT Q e ≠ 0) :
    secIdeal (Q.map (MvPolynomial.map (C : k →+* MvPolynomial (Par e n) k)))
      (X : Par e n → MvPolynomial (Par e n) k) ≤ RingHom.ker (Ψt Q e c) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«GenSecDomain».«secIdeal_le_ker» := P2M_GroundTheory_Heights__Heights_Vertical_GenSecDomain_secIdeal_le_ker_859e8674bf60
