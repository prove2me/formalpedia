-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_InhabA_submatrix_mul_blk
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.InhabA.submatrix_mul_blk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:06:03.045805+00:00
-- url     : https://prove2.me/theorems/d12e830a-b500-449f-859c-1d1e447c25f1
-- title:
--   Inhab A: submatrix mul blk
-- statement:
--   The Inhab A construction uses the submatrix mul blk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/InhabA.lean#L47-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/InhabA.lean#L47-L58

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

theorem ReciprocityTheory.ChartRestriction.DS.S7.InhabA.submatrix_mul_blk {ε : Fin m → Bool} (s : Bool) {g : Matrix (Fin m) (Fin m) ℂ}
    (hg : ∀ i j, ε i ≠ ε j → g i j = 0) (h : Matrix (Fin m) (Fin m) ℂ) :
    (g * h).submatrix (fun x : {a // ε a = s} => x.1) (fun x : {a // ε a = s} => x.1) =
      g.submatrix (fun x : {a // ε a = s} => x.1) (fun x : {a // ε a = s} => x.1) *
        h.submatrix (fun x : {a // ε a = s} => x.1) (fun x : {a // ε a = s} => x.1) := by sorry
