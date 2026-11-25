-- Prove2me | Theorems.Thm_SNumbers_idEmbed_apply
-- name    : SNumbers.idEmbed_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:38:42.298793+00:00
-- url     : https://prove2.me/theorems/8fd2c845-9a4e-5258-866d-7e10f0f23080
-- title:
--   SNumbers: id Embed apply
-- statement:
--   The SNumbers construction uses the id Embed apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/Identity.lean#L131-L132
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/Identity.lean#L131-L132

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

theorem SNumbers.idEmbed_apply {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (x : PiLp q (fun _ : Fin m => 𝕜)) (i : Fin m) : (idEmbed p q x) i = x i := by sorry

attribute [defeq] SNumbers.idEmbed_apply
