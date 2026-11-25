-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_pderiv_aeval_eq_sum_be961d70ab0c
-- name    : P2M_GroundTheory_Heights__Heights_pderiv_aeval_eq_sum_be961d70ab0c
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:50:14.408592+00:00
-- url     : https://prove2.me/theorems/ed859ad5-82b4-4776-9375-f5deeda4a1fc
-- title:
--   P2 M Ground Theory Heights  Heights pderiv aeval eq sum be961d70ab0c: P2 M Ground Theory Heights  Heights pderiv aeval eq sum be961d70ab0c
-- statement:
--   The P2 M Ground Theory Heights  Heights pderiv aeval eq sum be961d70ab0c construction uses the P2 M Ground Theory Heights  Heights pderiv aeval eq sum be961d70ab0c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChowFormBirational.lean#L11-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChowFormBirational.lean#L11-L27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChowFormBirational
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_pderiv_aeval_eq_sum_be961d70ab0c {F K : Type*} [CommRing F] [CommRing K] [Algebra F K]
    {σ τ : Type*} [Fintype σ] (ψ : σ → MvPolynomial τ K) (i : τ) (g : MvPolynomial σ F) :
    pderiv i (aeval ψ g) = ∑ j, aeval ψ (pderiv j g) * pderiv i (ψ j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«pderiv_aeval_eq_sum» := P2M_GroundTheory_Heights__Heights_pderiv_aeval_eq_sum_be961d70ab0c
