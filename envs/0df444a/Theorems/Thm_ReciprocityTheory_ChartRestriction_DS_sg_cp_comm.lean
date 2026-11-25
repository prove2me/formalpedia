-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_sg_cp_comm
-- name    : ReciprocityTheory.ChartRestriction.DS.sg_cp_comm
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T09:57:04.115408+00:00
-- url     : https://prove2.me/theorems/a15f2efc-b225-592c-85a8-869cf015d098
-- title:
--   DS: sg cp comm
-- statement:
--   The DS construction uses the sg cp comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFPrimeA.lean#L35-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFPrimeA.lean#L35-L74

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_InhabCAR
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFPrimeA
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
variable {n : ℕ}
variable {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem ReciprocityTheory.ChartRestriction.DS.sg_cp_comm {cp cm : Fin n → Fin n → Module.End ℂ W} (hC : IsCAR cp cm) (ε : Fin n → Bool)
    (c i x : Fin n) :
    sgE ε cp cm c c * cp i x = cp i x * sgE ε cp cm c c + ((modeWt ε (i, x) c : ℝ) : ℂ) • cp i x := by sorry
