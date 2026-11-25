-- Prove2me | Theorems.Thm_SNumbers_sn_id_piLp
-- name    : SNumbers.sn_id_piLp
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T05:25:09.276871+00:00
-- url     : https://prove2.me/theorems/ed0638a4-4c0b-5bfa-bbfa-c898549b49df
-- title:
--   SNumbers: sn id pi Lp
-- statement:
--   For every strict s-number sequence, the identity on `ℓ^p_m` has `sₙ(id) = 1`
--   whenever `n < m` (directly from (S5'), via `dim ℓ^p_m = m`).
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/DiagonalMatrices.lean#L327-L329
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/DiagonalMatrices.lean#L327-L329

module
public import Definitions.Def_SNumbers_Approximation
public import Definitions.Def_SNumbers_Bernstein
public import Definitions.Def_SNumbers_Gelfand
public import Definitions.Def_SNumbers_Kolmogorov
public import Definitions.Def_SNumbers_Hilbert
public import Definitions.Def_SNumbers_PiLpCoordinates
public import Definitions.Def_SNumbers_Examples_FlatnessLemmas
public import Definitions.Def_SNumbers_Examples_Identity
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.MeanInequalities
public import Definitions.Def_SNumbers_Examples_DiagonalMatrices
set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped ENNReal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜] {m : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem SNumbers.sn_id_piLp {s : Family 𝕜} (hs : IsStrictSNumberSequence s) {n : ℕ} (hn : n < m) :
    s (ContinuousLinearMap.id 𝕜 (PiLp p (fun _ : Fin m => 𝕜))) n = 1 := by sorry
