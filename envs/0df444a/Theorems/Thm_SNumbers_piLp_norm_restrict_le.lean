-- Prove2me | Theorems.Thm_SNumbers_piLp_norm_restrict_le
-- name    : SNumbers.piLp_norm_restrict_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:41:58.911808+00:00
-- url     : https://prove2.me/theorems/a4385c0e-0ea8-41f7-b031-8cfd548a6f42
-- title:
--   SNumbers: pi Lp norm restrict le
-- statement:
--   **Cross-exponent norm comparison, restricted to a finite support.** For
--   `1 ≤ p ≤ q` (with `q ≠ ∞`) and `f` supported on a finite set `s`,
--   `‖f‖_p ≤ (card s)^{1/p - 1/q} · ‖f‖_q`. The power-mean inequality, applied over
--   the support `s`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/Identity.lean#L57-L98
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/Identity.lean#L57-L98

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

theorem SNumbers.piLp_norm_restrict_le {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hpq : p ≤ q) (hq : q ≠ ∞) (s : Finset (Fin m)) (f : Fin m → 𝕜)
    (hf : ∀ i ∉ s, f i = 0) :
    ‖(WithLp.toLp p f : PiLp p (fun _ : Fin m => 𝕜))‖
      ≤ (s.card : ℝ) ^ (1 / p.toReal - 1 / q.toReal) *
        ‖(WithLp.toLp q f : PiLp q (fun _ : Fin m => 𝕜))‖ := by sorry
