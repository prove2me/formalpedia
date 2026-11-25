-- Prove2me | Theorems.Thm_SNumbers_Lifting_kolmogorovNumber_eq
-- name    : SNumbers.Lifting.kolmogorovNumber_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T03:13:36.30552+00:00
-- url     : https://prove2.me/theorems/6da2e81b-b790-4ca7-b0b1-2b2b84d364d8
-- title:
--   Lifting: kolmogorov Number eq
-- statement:
--   Restatement of Pietsch's identity as the agreement of the two definitions:
--   the lifting Kolmogorov number of this file coincides with the canonical one on
--   Banach spaces.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/KolmogorovLifting.lean#L736-L738
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/KolmogorovLifting.lean#L736-L738

module
public import Definitions.Def_SNumbers_Approximation
public import Definitions.Def_SNumbers_Kolmogorov
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_KolmogorovLifting
set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal NNReal ENNReal
open ContinuousLinearMap
open SNumbers
open SNumbers.Lifting
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [CompleteSpace X]
variable {𝕜 : Type u} [DenselyNormedField 𝕜] [CompleteSpace 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

theorem SNumbers.Lifting.kolmogorovNumber_eq (S : X →L[𝕜] Y) (n : ℕ) :
    kolmogorovNumber S n = SNumbers.kolmogorovNumber S n := by sorry
