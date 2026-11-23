-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_InhabA_star_det_mul_det
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.InhabA.star_det_mul_det
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:05:40.196271+00:00
-- url     : https://prove2.me/theorems/8a98ff30-7b70-47da-83c5-489859eed772
-- title:
--   Inhab A: star det mul det
-- statement:
--   The Inhab A construction uses the star det mul det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/InhabA.lean#L60-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/InhabA.lean#L60-L70

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

theorem ReciprocityTheory.ChartRestriction.DS.S7.InhabA.star_det_mul_det {ε : Fin m → Bool} (s : Bool) {k : Matrix (Fin m) (Fin m) ℂ} (hk : k ∈ Kset ε) :
    star (k.submatrix (fun x : {a // ε a = s} => x.1) (fun x : {a // ε a = s} => x.1)).det *
      (k.submatrix (fun x : {a // ε a = s} => x.1) (fun x : {a // ε a = s} => x.1)).det = 1 := by sorry
