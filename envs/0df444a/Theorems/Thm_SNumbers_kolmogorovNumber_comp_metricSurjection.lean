-- Prove2me | Theorems.Thm_SNumbers_kolmogorovNumber_comp_metricSurjection
-- name    : SNumbers.kolmogorovNumber_comp_metricSurjection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:10:48.164555+00:00
-- url     : https://prove2.me/theorems/b7b88d20-f13f-4fed-86c1-45ad929c92db
-- title:
--   SNumbers: kolmogorov Number comp metric Surjection
-- statement:
--   `dₙ(S ∘ Q) = dₙ(S)` for every metric surjection `Q`: the infimum sets
--   defining the two Kolmogorov numbers coincide term by term.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Injectivity.lean#L268-L279
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Injectivity.lean#L268-L279

module
public import Definitions.Def_SNumbers_Gelfand
public import Definitions.Def_SNumbers_Kolmogorov
public import Definitions.Def_SNumbers_Injectivity
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

theorem SNumbers.kolmogorovNumber_comp_metricSurjection {Q : W →L[𝕜] X}
    (hQ : IsMetricSurjection Q) (S : X →L[𝕜] Y) (n : ℕ) :
    kolmogorovNumber (S.comp Q) n = kolmogorovNumber S n := by sorry
