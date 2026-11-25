-- Prove2me | Theorems.Thm_SNumbers_piLp_norm_le_of_exponent_ge
-- name    : SNumbers.piLp_norm_le_of_exponent_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T04:12:49.375057+00:00
-- url     : https://prove2.me/theorems/d75f30da-ca18-4721-ae6e-1a240c3415ed
-- title:
--   SNumbers: pi Lp norm le of exponent ge
-- statement:
--   **`L^p`-norm monotonicity in the exponent** on a finite product: for `q ≤ p`,
--   `‖x‖_p ≤ ‖x‖_q` (the same underlying vector, re-measured). Mathlib has no `PiLp`
--   version; a candidate for upstreaming.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/DiagonalMatrices.lean#L896-L972
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/DiagonalMatrices.lean#L896-L972

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
variable {q : ℝ≥0∞} [Fact (1 ≤ q)]

theorem SNumbers.piLp_norm_le_of_exponent_ge [Nonempty (Fin m)] (hqp : q ≤ p) (f : Fin m → 𝕜) :
    ‖(WithLp.toLp p f : PiLp p (fun _ : Fin m => 𝕜))‖
      ≤ ‖(WithLp.toLp q f : PiLp q (fun _ : Fin m => 𝕜))‖ := by sorry
