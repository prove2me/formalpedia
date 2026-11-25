-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_sg_prod_list
-- name    : ReciprocityTheory.ChartRestriction.DS.sg_prod_list
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T09:54:32.322147+00:00
-- url     : https://prove2.me/theorems/32ddbbfc-fdfd-4502-9ecd-024df6cedfb0
-- title:
--   DS: sg prod list
-- statement:
--   The DS construction uses the sg prod list property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFPrimeA.lean#L82-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFPrimeA.lean#L82-L100

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

theorem ReciprocityTheory.ChartRestriction.DS.sg_prod_list (ε : Fin n → Bool) (c : Fin n) (l : List (Fin n × Fin n)) :
    sgE ε cpFock cmFock c c (l.map fun x => ExteriorAlgebra.ι ℂ (Pi.single x (1 : ℂ))).prod =
      (((l.map fun x => modeWt ε x c).sum : ℝ) : ℂ) •
        (l.map fun x => ExteriorAlgebra.ι ℂ (Pi.single x (1 : ℂ))).prod := by sorry
