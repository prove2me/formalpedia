-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_MongeAmpereIntegrability_det_updateCol_eq
-- name    : ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.det_updateCol_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:57:11.027204+00:00
-- url     : https://prove2.me/theorems/ae2bcc11-456c-5d67-a351-b6bb189b38f4
-- title:
--   Monge Ampere Integrability: det update Col eq
-- statement:
--   The Monge Ampere Integrability construction uses the det update Col eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/DetUpdateColEq.lean#L114-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/DetUpdateColEq.lean#L114-L122

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_IntegralFderivApplyEqZero
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_DifferentiableAtChart
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_DetUpdateColEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability
open MeasureTheory Filter Topology Set
open scoped ContDiff
noncomputable section
variable {n : ℕ}

theorem ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.det_updateCol_eq (M : Matrix (Fin n) (Fin n) ℂ) (k : Fin n) (b : Fin n → ℂ) :
    (M.updateCol k b).det = ∑ σ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * (b (σ k) * ∏ l ∈ Finset.univ.erase k, M (σ l) l) := by sorry
