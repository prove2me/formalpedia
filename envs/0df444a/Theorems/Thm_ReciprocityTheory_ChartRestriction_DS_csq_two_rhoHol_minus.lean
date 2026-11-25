-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_csq_two_rhoHol_minus
-- name    : ReciprocityTheory.ChartRestriction.DS.csq_two_rhoHol_minus
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T09:49:07.513014+00:00
-- url     : https://prove2.me/theorems/82ba73df-ca23-438f-bb6d-4abd0e41c2bd
-- title:
--   DS: csq two rho Hol minus
-- statement:
--   The DS construction uses the csq two rho Hol minus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CARSqA.lean#L72-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CARSqA.lean#L72-L77

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CarSumSqZeroOfAnti
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARSqA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem ReciprocityTheory.ChartRestriction.DS.csq_two_rhoHol_minus (ε : Fin n → Bool) {a : Fin n} (ha : a ∈ minusIdx ε) :
    (2 : ℂ) * ((rhoHol ε a : ℝ) : ℂ) = -(pOf ε : ℂ) := by sorry
