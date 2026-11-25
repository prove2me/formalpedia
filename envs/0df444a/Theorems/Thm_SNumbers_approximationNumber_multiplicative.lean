-- Prove2me | Theorems.Thm_SNumbers_approximationNumber_multiplicative
-- name    : SNumbers.approximationNumber_multiplicative
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:20:54.655721+00:00
-- url     : https://prove2.me/theorems/f23666fa-f5ef-4efd-98f7-677e8c2ceec8
-- title:
--   SNumbers: approximation Number multiplicative
-- statement:
--   **Multiplicativity of the approximation numbers**: for `T : X → Y` and `S : Y → Z`,
--   `a_{n+m}(S ∘ T) ≤ aₙ(S) · a_m(T)`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Approximation.lean#L230-L251
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Approximation.lean#L230-L251

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Approximation
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

theorem SNumbers.approximationNumber_multiplicative (S : Y →L[𝕜] Z) (T : X →L[𝕜] Y) (n m : ℕ) :
    approximationNumber (S.comp T) (n + m) ≤
      approximationNumber S n * approximationNumber T m := by sorry
