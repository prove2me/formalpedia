-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SecAlgField_genPar_algebraicIndependent_e5b691f6d8b9
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_SecAlgField_genPar_algebraicIndependent_e5b691f6d8b9
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:43:25.673902+00:00
-- url     : https://prove2.me/theorems/06ad677b-a173-4c7c-9d3f-4487efaa8de8
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Sec Alg Field gen Par algebraic Independent e5b691f6d8b9: P2 M Ground Theory Heights  Heights Vertical Sec Alg Field gen Par algebraic Independent e5b691f6
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Sec Alg Field gen Par algebraic Independent e5b691f6d8b9 construction uses the P2 M Ground Theory Heights  Heights Vertical Sec Alg Field gen Par algebraic Independent e5b691f6d8b9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecAlgField.lean#L14-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecAlgField.lean#L14-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_ComapMaximalIdealParDVR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecAlgField
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
open GroundTheory.Heights₂.Heights.Vertical.SecAlgField

theorem P2M_GroundTheory_Heights__Heights_Vertical_SecAlgField_genPar_algebraicIndependent_e5b691f6d8b9 (k : Type*) [Field k] (e n : ℕ) :
    AlgebraicIndependent k (genPar k e n) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«SecAlgField».«genPar_algebraicIndependent» := P2M_GroundTheory_Heights__Heights_Vertical_SecAlgField_genPar_algebraicIndependent_e5b691f6d8b9
