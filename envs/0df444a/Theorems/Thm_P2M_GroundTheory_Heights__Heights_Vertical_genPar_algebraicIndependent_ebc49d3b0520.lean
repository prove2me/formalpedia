-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_genPar_algebraicIndependent_ebc49d3b0520
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_genPar_algebraicIndependent_ebc49d3b0520
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:44:40.797279+00:00
-- url     : https://prove2.me/theorems/20ebf7e3-97ec-4967-86cd-4c52ea79a168
-- title:
--   P2 M Ground Theory Heights  Heights Vertical gen Par algebraic Independent ebc49d3b0520: P2 M Ground Theory Heights  Heights Vertical gen Par algebraic Independent ebc49d3b0520
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical gen Par algebraic Independent ebc49d3b0520 construction uses the P2 M Ground Theory Heights  Heights Vertical gen Par algebraic Independent ebc49d3b0520 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PChowNormFormGeneric.lean#L11-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PChowNormFormGeneric.lean#L11-L21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PChowNormFormGeneric
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

theorem P2M_GroundTheory_Heights__Heights_Vertical_genPar_algebraicIndependent_ebc49d3b0520 (k : Type*) [Field k] (e n : ℕ) :
    AlgebraicIndependent k (genPar k e n) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«genPar_algebraicIndependent» := P2M_GroundTheory_Heights__Heights_Vertical_genPar_algebraicIndependent_ebc49d3b0520
