-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_eval_coneFirstForm_bc87d2d7c017
-- name    : P2M_GroundTheory_Heights__Heights_eval_coneFirstForm_bc87d2d7c017
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:46:10.461163+00:00
-- url     : https://prove2.me/theorems/a0a9c224-eea2-42ea-89e8-7ea403584390
-- title:
--   P2 M Ground Theory Heights  Heights eval cone First Form bc87d2d7c017: P2 M Ground Theory Heights  Heights eval cone First Form bc87d2d7c017
-- statement:
--   The P2 M Ground Theory Heights  Heights eval cone First Form bc87d2d7c017 construction uses the P2 M Ground Theory Heights  Heights eval cone First Form bc87d2d7c017 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsConeProjHyperplaneDim.lean#L17-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsConeProjHyperplaneDim.lean#L17-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeProjHyperplaneNull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeProjHyperplaneDim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj segre)

theorem P2M_GroundTheory_Heights__Heights_eval_coneFirstForm_bc87d2d7c017 {n e : ℕ} (Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (z : Fin n → ℂ) : eval z (coneFirstForm Ψ) = Ψ (segre fun p : Σ k, PBlk n k => z p.2) 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«eval_coneFirstForm» := P2M_GroundTheory_Heights__Heights_eval_coneFirstForm_bc87d2d7c017
