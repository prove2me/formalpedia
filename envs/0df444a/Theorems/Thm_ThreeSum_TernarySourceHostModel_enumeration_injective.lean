-- Prove2me | Theorems.Thm_ThreeSum_TernarySourceHostModel_enumeration_injective
-- name    : ThreeSum.TernarySourceHostModel.enumeration_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:56:49.214132+00:00
-- url     : https://prove2.me/theorems/c039422f-a68b-4159-bb7a-37768a93a4a2
-- title:
--   Ternary Source Host Model: enumeration injective
-- statement:
--   The Ternary Source Host Model construction uses the enumeration injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySourceHostModel.lean#L114-L126
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySourceHostModel.lean#L114-L126

import Definitions.Def_Submission_ThreeSum_LightTernarySourceHost
import Definitions.Def_Submission_ThreeSum_TernaryWeightedPhysicalSources
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_Submission_ThreeSum_TernarySourceHostModel
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernarySourceHostModel
open Finset Light TernaryJointType
open scoped BigOperators
variable {N : ℕ}

theorem ThreeSum.TernarySourceHostModel.enumeration_injective (enumeration : ℕ → TritWord N) (bank : ℕ)
    (hsorted : ∀ i j, i<j → j<bank →
      TernaryCodeSemantics.address (enumeration i)<TernaryCodeSemantics.address (enumeration j)) :
    ∀ i j, i<bank → j<bank → enumeration i=enumeration j → i=j := by sorry
