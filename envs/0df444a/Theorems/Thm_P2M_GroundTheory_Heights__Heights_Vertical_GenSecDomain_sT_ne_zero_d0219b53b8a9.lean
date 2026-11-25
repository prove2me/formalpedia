-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_GenSecDomain_sT_ne_zero_d0219b53b8a9
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_GenSecDomain_sT_ne_zero_d0219b53b8a9
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:42:58.025865+00:00
-- url     : https://prove2.me/theorems/34b061a0-73f0-4286-b7d8-76daf1ca0ee0
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Gen Sec Domain s T ne zero d0219b53b8a9: P2 M Ground Theory Heights  Heights Vertical Gen Sec Domain s T ne zero d0219b53b8a9
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Gen Sec Domain s T ne zero d0219b53b8a9 construction uses the P2 M Ground Theory Heights  Heights Vertical Gen Sec Domain s T ne zero d0219b53b8a9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PGenSecDomain.lean#L101-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PGenSecDomain.lean#L101-L105

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

theorem P2M_GroundTheory_Heights__Heights_Vertical_GenSecDomain_sT_ne_zero_d0219b53b8a9 (j : Fin n) (hj : genPt Q j ≠ 0) : sT Q e ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«GenSecDomain».«sT_ne_zero» := P2M_GroundTheory_Heights__Heights_Vertical_GenSecDomain_sT_ne_zero_d0219b53b8a9
