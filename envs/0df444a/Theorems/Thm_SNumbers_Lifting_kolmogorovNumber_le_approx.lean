-- Prove2me | Theorems.Thm_SNumbers_Lifting_kolmogorovNumber_le_approx
-- name    : SNumbers.Lifting.kolmogorovNumber_le_approx
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:54:25.583526+00:00
-- url     : https://prove2.me/theorems/003478fe-1788-47cf-b44c-f690de9ea8a8
-- title:
--   Lifting: kolmogorov Number le approx
-- statement:
--   **Pietsch's identity, `(≤)` half:** `dₙ(S) ≤ aₙ(S ∘ Q)`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/KolmogorovLifting.lean#L571-L594
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/KolmogorovLifting.lean#L571-L594

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
omit [CompleteSpace 𝕜]

theorem SNumbers.Lifting.kolmogorovNumber_le_approx (S : X →L[𝕜] Y) (n : ℕ) :
    SNumbers.kolmogorovNumber S n
      ≤ approximationNumber (S.comp (Q : BallLp 𝕜 X →L[𝕜] X)) n := by sorry
