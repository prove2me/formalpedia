-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_InhabA_det_ne_zero
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.InhabA.det_ne_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:44:32.920542+00:00
-- url     : https://prove2.me/theorems/55514add-3b20-46d0-865a-ac0e4322767b
-- title:
--   Inhab A: det ne zero
-- statement:
--   The Inhab A construction uses the det ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/InhabA.lean#L72-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/InhabA.lean#L72-L77

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

theorem ReciprocityTheory.ChartRestriction.DS.S7.InhabA.det_ne_zero {ε : Fin m → Bool} (s : Bool) {k : Matrix (Fin m) (Fin m) ℂ} (hk : k ∈ Kset ε) :
    (k.submatrix (fun x : {a // ε a = s} => x.1) (fun x : {a // ε a = s} => x.1)).det ≠ 0 := by sorry
