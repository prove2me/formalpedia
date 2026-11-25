-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_InhabA_hasDerivAt_blockDet
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.InhabA.hasDerivAt_blockDet
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:48:12.612207+00:00
-- url     : https://prove2.me/theorems/df888245-a2d8-5757-aa52-9748b513b3c5
-- title:
--   Inhab A: has Deriv At block Det
-- statement:
--   The Inhab A construction uses the has Deriv At block Det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/InhabA.lean#L79-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/InhabA.lean#L79-L94

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

theorem ReciprocityTheory.ChartRestriction.DS.S7.InhabA.hasDerivAt_blockDet (ε : Fin m → Bool) (s : Bool) (X : Matrix (Fin m) (Fin m) ℂ) :
    HasDerivAt (fun t : ℝ => ((NormedSpace.exp ((t : ℂ) • X)).submatrix
        (fun x : {a // ε a = s} => x.1) (fun x : {a // ε a = s} => x.1)).det)
      (∑ a ∈ univ.filter (fun a => ε a = s), X a a) 0 := by sorry
