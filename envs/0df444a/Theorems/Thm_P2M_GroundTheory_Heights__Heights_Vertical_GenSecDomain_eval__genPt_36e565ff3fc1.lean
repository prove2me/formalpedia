-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_GenSecDomain_eval__genPt_36e565ff3fc1
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_GenSecDomain_eval__genPt_36e565ff3fc1
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:42:30.544799+00:00
-- url     : https://prove2.me/theorems/d9153609-4f74-5f17-9abf-eca9c65ce991
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Gen Sec Domain eval  gen Pt 36e565ff3fc1: P2 M Ground Theory Heights  Heights Vertical Gen Sec Domain eval  gen Pt 36e565ff3fc1
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Gen Sec Domain eval  gen Pt 36e565ff3fc1 construction uses the P2 M Ground Theory Heights  Heights Vertical Gen Sec Domain eval  gen Pt 36e565ff3fc1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PGenSecDomain.lean#L90-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PGenSecDomain.lean#L90-L99

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

theorem P2M_GroundTheory_Heights__Heights_Vertical_GenSecDomain_eval__genPt_36e565ff3fc1 (p : MvPolynomial (Fin n) k) :
    eval₂ (algebraMap k (Fn Q)) (genPt Q) p = algebraMap _ (Fn Q) (Ideal.Quotient.mk Q p) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«GenSecDomain».«eval₂_genPt» := P2M_GroundTheory_Heights__Heights_Vertical_GenSecDomain_eval__genPt_36e565ff3fc1
