-- Prove2me | Theorems.Thm_SNumbers_kolmogorovNumber_eq_approx
-- name    : SNumbers.kolmogorovNumber_eq_approx
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:57:03.48563+00:00
-- url     : https://prove2.me/theorems/a1b214eb-ec9e-4c58-b451-5c9cd74ebdbb
-- title:
--   SNumbers: kolmogorov Number eq approx
-- statement:
--   **Pietsch's identity.** On a Banach domain `X`, the canonical Kolmogorov
--   number `SNumbers.kolmogorovNumber S n` (the quotient/inf-sup form from
--   `SNumbers.Kolmogorov`, valid on any normed space) equals the approximation
--   number of the lift `S ∘ Q`, where `Q : ℓ¹(B_X) →L[𝕜] X` is the summation
--   surjection. This identifies the two developments of the Kolmogorov numbers.
--   `[CompleteSpace X]` makes `Q` a continuous map into `X` (it is an infinite
--   series); `[CompleteSpace 𝕜]` makes the finite-dimensional subspace that
--   carries the lifted approximant complete.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/KolmogorovLifting.lean#L728-L731
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/KolmogorovLifting.lean#L728-L731

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

theorem SNumbers.kolmogorovNumber_eq_approx (S : X →L[𝕜] Y) (n : ℕ) :
    SNumbers.kolmogorovNumber S n
      = approximationNumber (S.comp (Q : BallLp 𝕜 X →L[𝕜] X)) n := by sorry
