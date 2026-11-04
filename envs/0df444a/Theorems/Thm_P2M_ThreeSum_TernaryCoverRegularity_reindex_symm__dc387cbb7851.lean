-- Prove2me | Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851
-- name    : P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:52:22.107794+00:00
-- url     : https://prove2.me/theorems/21525793-63a5-4894-ab87-da4b0e27f9a5
-- title:
--   P2 M Three Sum Ternary Cover Regularity reindex symm  dc387cbb7851: P2 M Three Sum Ternary Cover Regularity reindex symm  dc387cbb7851
-- statement:
--   The P2 M Three Sum Ternary Cover Regularity reindex symm  dc387cbb7851 construction uses the P2 M Three Sum Ternary Cover Regularity reindex symm  dc387cbb7851 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverRegularity.lean#L60-L63
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverRegularity.lean#L60-L63

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryCoverRegularity
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverRegularity
open Finset TernaryJointType TernaryCoverLocal
variable {L : ℕ}

theorem P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851 (σ : Equiv.Perm (Fin L)) (w : TritWord L) :
    reindex σ (reindex σ.symm w) = w := by sorry

alias «ThreeSum».«TernaryCoverRegularity».«reindex_symm'» := P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851
