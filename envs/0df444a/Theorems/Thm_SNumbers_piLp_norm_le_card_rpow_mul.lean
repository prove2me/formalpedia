-- Prove2me | Theorems.Thm_SNumbers_piLp_norm_le_card_rpow_mul
-- name    : SNumbers.piLp_norm_le_card_rpow_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:58:41.848044+00:00
-- url     : https://prove2.me/theorems/68745681-b9d5-4863-8e43-cbf0a2f570cc
-- title:
--   SNumbers: pi Lp norm le card rpow mul
-- statement:
--   **Cross-exponent norm comparison** on all of `ℓ^p_m`: for `1 ≤ p ≤ q`
--   (`q ≠ ∞`), `‖f‖_p ≤ m^{1/p - 1/q} · ‖f‖_q`. Sharp, with equality at the
--   all-ones vector.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/Identity.lean#L103-L109
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/Identity.lean#L103-L109

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

theorem SNumbers.piLp_norm_le_card_rpow_mul {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hpq : p ≤ q) (hq : q ≠ ∞) (f : Fin m → 𝕜) :
    ‖(WithLp.toLp p f : PiLp p (fun _ : Fin m => 𝕜))‖
      ≤ (m : ℝ) ^ (1 / p.toReal - 1 / q.toReal) *
        ‖(WithLp.toLp q f : PiLp q (fun _ : Fin m => 𝕜))‖ := by sorry
