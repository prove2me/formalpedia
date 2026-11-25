-- Prove2me | Theorems.Thm_SNumbers_exists_next_vector
-- name    : SNumbers.exists_next_vector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T04:27:52.631787+00:00
-- url     : https://prove2.me/theorems/2feca69e-dc97-50b7-badc-ab81ce4469bd
-- title:
--   SNumbers: exists next vector
-- statement:
--   **Analytic heart of the construction.** Given functionals `ρ'` and `m ≤ n`,
--   if `γ < cₙ(S)` there is a unit-image vector `eₘ` (`‖S eₘ‖ = 1`, `‖eₘ‖ ≤ 1/γ`) in
--   `⋂_i ker(ρ'ᵢ∘S)` and a norming functional `ρₘ`. The kernel `N` is closed with
--   `codim ≤ m ≤ n`, so `cₙ(S) ≤ ‖S|_N‖` supplies the stretched vector.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Inequalities.lean#L196-L239
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Inequalities.lean#L196-L239

module
public import Definitions.Def_SNumbers_Hilbert
public import Definitions.Def_SNumbers_Uniqueness
public import Definitions.Def_SNumbers_Bernstein
public import Definitions.Def_SNumbers_Gelfand
public import Definitions.Def_SNumbers_Kolmogorov
public import Definitions.Def_SNumbers_SingularValuesFinDim
public import Definitions.Def_BasicResults_GarlingGordon
public import Definitions.Def_BasicResults_KadetsSnobar
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Definitions.Def_SNumbers_Inequalities
set_option autoImplicit true
@[expose] public section
public section
universe u
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

theorem SNumbers.exists_next_vector (S : X →L[𝕜] Y) {n : ℕ} {γ : ℝ} (hγ : 0 < γ)
    (hγc : γ < gelfandNumber S n) {m : ℕ} (hm : m ≤ n) (ρ' : Fin m → (Y →L[𝕜] 𝕜)) :
    ∃ (em : X) (ρm : Y →L[𝕜] 𝕜),
      ‖S em‖ = 1 ∧ ‖em‖ ≤ 1 / γ ∧ ‖ρm‖ = 1 ∧ ρm (S em) = (‖S em‖ : 𝕜) ∧
      (∀ i : Fin m, ρ' i (S em) = 0) := by sorry
