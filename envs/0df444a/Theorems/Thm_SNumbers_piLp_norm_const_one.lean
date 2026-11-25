-- Prove2me | Theorems.Thm_SNumbers_piLp_norm_const_one
-- name    : SNumbers.piLp_norm_const_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:58:32.728543+00:00
-- url     : https://prove2.me/theorems/1448f03c-ff63-52ef-b47c-73e39fbc5cad
-- title:
--   SNumbers: pi Lp norm const one
-- statement:
--   The `L^p` norm of the all-ones vector on `Fin m` is `m^{1/p}`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/Identity.lean#L112-L118
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/Identity.lean#L112-L118

module
public import Definitions.Def_SNumbers_Approximation
public import Definitions.Def_SNumbers_Examples_FlatnessLemmas
public import Mathlib.Analysis.MeanInequalities
public import Definitions.Def_SNumbers_Examples_Identity
set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped ENNReal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜] {m : ℕ}

theorem SNumbers.piLp_norm_const_one {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    ‖(WithLp.toLp p (fun _ : Fin m => (1 : 𝕜)))‖ = (m : ℝ) ^ (1 / p.toReal) := by sorry
