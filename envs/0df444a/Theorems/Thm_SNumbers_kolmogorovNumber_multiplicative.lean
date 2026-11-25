-- Prove2me | Theorems.Thm_SNumbers_kolmogorovNumber_multiplicative
-- name    : SNumbers.kolmogorovNumber_multiplicative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:28:42.099036+00:00
-- url     : https://prove2.me/theorems/875e1099-5976-45cb-b88b-9fe9b4372631
-- title:
--   SNumbers: kolmogorov Number multiplicative
-- statement:
--   **Multiplicativity of the Kolmogorov numbers**: for `T : X → Y` and `S : Y → Z`,
--   `d_{n+m}(S ∘ T) ≤ dₙ(S) · d_m(T)`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Kolmogorov.lean#L335-L368
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Kolmogorov.lean#L335-L368

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

theorem SNumbers.kolmogorovNumber_multiplicative (S : Y →L[𝕜] Z) (T : X →L[𝕜] Y) (n m : ℕ) :
    kolmogorovNumber (S.comp T) (n + m) ≤ kolmogorovNumber S n * kolmogorovNumber T m := by sorry
