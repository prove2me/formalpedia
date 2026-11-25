-- Prove2me | Theorems.Thm_SNumbers_Lifting_kolmogorovNumber_strict
-- name    : SNumbers.Lifting.kolmogorovNumber_strict
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:54:03.493896+00:00
-- url     : https://prove2.me/theorems/a513d1a8-2673-58d2-8957-9f6cf9545821
-- title:
--   Lifting: kolmogorov Number strict
-- statement:
--   (S5') Strict normalisation `kolmogorovNumber id_X n = 1` whenever `dim X > n`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/KolmogorovLifting.lean#L518-L527
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/KolmogorovLifting.lean#L518-L527

module
public import Definitions.Def_SNumbers_Approximation
public import Definitions.Def_SNumbers_Kolmogorov
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_KolmogorovLifting
public import Theorems.Thm_SNumbers_kolmogorovNumber_strict

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
variable {X : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

theorem SNumbers.Lifting.kolmogorovNumber_strict (n : ℕ) (h : (n : Cardinal) < Module.rank 𝕜 X) :
    kolmogorovNumber (ContinuousLinearMap.id 𝕜 X) n = 1 := by sorry
