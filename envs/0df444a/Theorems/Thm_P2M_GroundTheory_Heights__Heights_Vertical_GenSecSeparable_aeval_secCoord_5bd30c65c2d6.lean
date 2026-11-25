-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_GenSecSeparable_aeval_secCoord_5bd30c65c2d6
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_GenSecSeparable_aeval_secCoord_5bd30c65c2d6
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:42:55.787389+00:00
-- url     : https://prove2.me/theorems/4432813c-9a9a-4d35-a2cd-68eb6ad36d1b
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Gen Sec Separable aeval sec Coord 5bd30c65c2d6: P2 M Ground Theory Heights  Heights Vertical Gen Sec Separable aeval sec Coord 5bd30c65c2d6
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Gen Sec Separable aeval sec Coord 5bd30c65c2d6 construction uses the P2 M Ground Theory Heights  Heights Vertical Gen Sec Separable aeval sec Coord 5bd30c65c2d6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PGenSecSeparable.lean#L55-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PGenSecSeparable.lean#L55-L73

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChartPointTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsSecPointSeparable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PGenSecSeparable
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
open GroundTheory.Heights₂.Heights.Vertical.GenSecSeparable

theorem P2M_GroundTheory_Heights__Heights_Vertical_GenSecSeparable_aeval_secCoord_5bd30c65c2d6 (k : Type*) [Field k] (e : ℕ) {n : ℕ} (Q : Ideal (MvPolynomial (Fin n) k))
    (f : MvPolynomial (Fin n) k) (hf : f ∈ Q) :
    aeval (secCoord (Q.map (MvPolynomial.map (algebraMap k (GenParField k e n)))) (genPar k e n)) f = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«GenSecSeparable».«aeval_secCoord» := P2M_GroundTheory_Heights__Heights_Vertical_GenSecSeparable_aeval_secCoord_5bd30c65c2d6
