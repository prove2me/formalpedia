-- Prove2me | Theorems.Thm_SNumbers_approximationNumber_additive
-- name    : SNumbers.approximationNumber_additive
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:13:40.707185+00:00
-- url     : https://prove2.me/theorems/cd127b34-1431-4c26-a8d7-a75897ca6dbf
-- title:
--   SNumbers: approximation Number additive
-- statement:
--   **Additivity of the approximation numbers**:
--   `a_{n+m}(S + T) ≤ aₙ(S) + a_m(T)`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Approximation.lean#L187-L198
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Approximation.lean#L187-L198

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

theorem SNumbers.approximationNumber_additive (S T : X →L[𝕜] Y) (n m : ℕ) :
    approximationNumber (S + T) (n + m) ≤
      approximationNumber S n + approximationNumber T m := by sorry
