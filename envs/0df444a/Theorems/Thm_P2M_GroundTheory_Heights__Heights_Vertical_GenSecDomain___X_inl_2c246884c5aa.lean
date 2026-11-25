-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_GenSecDomain___X_inl_2c246884c5aa
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_GenSecDomain___X_inl_2c246884c5aa
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:41:59.758378+00:00
-- url     : https://prove2.me/theorems/474915c9-f5f9-594e-9fa7-b864d99d1751
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Gen Sec Domain   X inl 2c246884c5aa: P2 M Ground Theory Heights  Heights Vertical Gen Sec Domain   X inl 2c246884c5aa
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Gen Sec Domain   X inl 2c246884c5aa construction uses the P2 M Ground Theory Heights  Heights Vertical Gen Sec Domain   X inl 2c246884c5aa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PGenSecDomain.lean#L61-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PGenSecDomain.lean#L61-L63

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

theorem P2M_GroundTheory_Heights__Heights_Vertical_GenSecDomain___X_inl_2c246884c5aa (c : Fin n → Fn Q) (i : Fin e) (j : Fin n) :
    ρ Q e c (X (.inl (i, j))) = C (genSubst (genPt Q) c (i, j)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«GenSecDomain».«ρ_X_inl» := P2M_GroundTheory_Heights__Heights_Vertical_GenSecDomain___X_inl_2c246884c5aa
