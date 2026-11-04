-- Prove2me | Theorems.Thm_ThreeSum_ExplicitLayers_valueSum_eq_explicit
-- name    : ThreeSum.ExplicitLayers.valueSum_eq_explicit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:16:09.489016+00:00
-- url     : https://prove2.me/theorems/dba3b784-b160-4168-ac51-8d87a40ab355
-- title:
--   Explicit Layers: value Sum eq explicit
-- statement:
--   The Explicit Layers construction uses the value Sum eq explicit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ExplicitLayers.lean#L50-L55
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ExplicitLayers.lean#L50-L55

import Definitions.Def_Submission_ThreeSum_SignedLeaf
import Definitions.Def_Submission_ThreeSum_SparseBoxes
import Definitions.Def_Submission_ThreeSum_ExplicitLayers
set_option autoImplicit false
open ThreeSum ThreeSum.ExplicitLayers
open Finset ThreeSum.SubsetAddress
open scoped BigOperators

theorem ThreeSum.ExplicitLayers.valueSum_eq_explicit {W : ℕ} (Q : Finset (Fin W)) (weight : Finset (Fin W) → ℤ) (t : ℕ) :
    valueSum Q weight t = ∑ S ∈ SparseBoxes.explicitLeaves Q t, weight S := by sorry
