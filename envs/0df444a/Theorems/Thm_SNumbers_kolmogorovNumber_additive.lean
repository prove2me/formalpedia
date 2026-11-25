-- Prove2me | Theorems.Thm_SNumbers_kolmogorovNumber_additive
-- name    : SNumbers.kolmogorovNumber_additive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:28:26.310907+00:00
-- url     : https://prove2.me/theorems/42c8c223-6cc0-444d-8afb-872039f20389
-- title:
--   SNumbers: kolmogorov Number additive
-- statement:
--   **Additivity of the Kolmogorov numbers**: `d_{n+m}(S + T) ≤ dₙ(S) + d_m(T)`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Kolmogorov.lean#L308-L331
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Kolmogorov.lean#L308-L331

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Definitions.Def_SNumbers_QuotientMapNorms
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Kolmogorov
set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

theorem SNumbers.kolmogorovNumber_additive (S T : X →L[𝕜] Y) (n m : ℕ) :
    kolmogorovNumber (S + T) (n + m) ≤ kolmogorovNumber S n + kolmogorovNumber T m := by sorry
