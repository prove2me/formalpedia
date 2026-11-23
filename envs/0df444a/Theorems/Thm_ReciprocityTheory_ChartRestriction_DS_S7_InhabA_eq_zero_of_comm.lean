-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_InhabA_eq_zero_of_comm
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.InhabA.eq_zero_of_comm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:05:51.894819+00:00
-- url     : https://prove2.me/theorems/4cfaadad-b049-4c1e-974f-e408021643a9
-- title:
--   Inhab A: eq zero of comm
-- statement:
--   The Inhab A construction uses the eq zero of comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/InhabA.lean#L35-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/InhabA.lean#L35-L45

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_Lemmata_MovedPointExistence_ExistsMoved
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_InhabA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 ReciprocityTheory.ChartRestriction.DS.S7.InhabA
open ReciprocityTheory.ChartRestriction.DS
variable {m : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.S7.InhabA.eq_zero_of_comm {ε : Fin m → Bool} {g : Matrix (Fin m) (Fin m) ℂ} (hg : g * Jm ε = Jm ε * g)
    (i j : Fin m) (hij : ε i ≠ ε j) : g i j = 0 := by sorry
