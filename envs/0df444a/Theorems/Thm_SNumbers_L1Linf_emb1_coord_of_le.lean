-- Prove2me | Theorems.Thm_SNumbers_L1Linf_emb1_coord_of_le
-- name    : SNumbers.L1Linf.emb1_coord_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:13:50.167904+00:00
-- url     : https://prove2.me/theorems/0779f388-472e-5ff4-9158-508f0d146458
-- title:
--   L1 Linf: emb1 coord of le
-- statement:
--   Coordinates of `emb1 v` beyond its support vanish.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L339-L346
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L339-L346

module
public import Definitions.Def_SNumbers_Gelfand
public import Definitions.Def_SNumbers_Hilbert
public import Definitions.Def_SNumbers_MaxDifference
public import Definitions.Def_BasicResults_LittleGrothendieck
public import Definitions.Def_BasicResults_SVD
public import Definitions.Def_AddOns_Approximable
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.Sequences
public import Definitions.Def_SNumbers_Examples_IdentityL1Linfty
set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open SNumbers SNumbers.L1Linf
variable {𝕜 : Type*} [RCLike 𝕜]

theorem SNumbers.L1Linf.emb1_coord_of_le (m : ℕ) (v : EuclideanSpace 𝕜 (Fin m)) {j : ℕ} (hj : m ≤ j) :
    (emb1 m v) j = 0 := by sorry
