-- Prove2me | Theorems.Thm_SeqExpDiffusion_eq_12_exists
-- name    : SeqExpDiffusion.eq_12_exists
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:10:09.941626+00:00
-- url     : https://prove2.me/theorems/123c8927-f6ed-4286-9980-e1423f6d76c5
-- title:
--   (12), p.17 — the belief diffusion exists for every initial belief
-- statement:
--   For every volatility $\tilde\sigma>0$ and every initial belief $\delta_0\in[0,1]$ there exist a probability space, a filtration, a Brownian motion $W$ for it and a process $\tilde\delta$ with continuous paths in $[0,1]$ solving
--
--   $$d\tilde\delta_t=\tilde\sigma\,\tilde\delta_t(1-\tilde\delta_t)\,dW_t,\qquad\tilde\delta_0=\delta_0.$$
--
--   The stopping problem (12) is posed on this diffusion; its existence is what makes the value function of (12) a non-vacuous notion.
--
--   Differences from the source:
--   - reading: (12) takes the solution δ̃ as given ("δ̃_t is a diffusion process solution of the SDE", Proposition 2, p.15) → existence of a solution is stated as a theorem; reason: the value statements quantify over all solutions and would be vacuous without one
--   - encoding: σ̃ is a volatility, with no stated sign → σ̃ > 0; reason: the paper uses it silently; only the degenerate σ̃ ≤ 0 is excluded
--   - encoding: a solution of the SDE → an adapted process with continuous paths in [0, 1] for every ω, solving the SDE through the published Itô relation, on a probability space in Type; reason: Lean conventions; same solutions
-- source:
--   Araman & Caldentey, Diffusion Approximations for a Class of Sequential Testing Problems, arXiv:2102.07030v3, display (12), p.17; Proposition 2, p.15

import Definitions.Def_SeqExpDiffusion_IsBeliefDiffusion

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace SeqExpDiffusion

/-- The belief diffusion (12) exists: for every `σ̃ > 0` and every initial belief `δ₀ ∈ [0, 1]` there
are a probability space, a filtration, a Brownian motion `W` for it and a solution of
`dδ̃_t = σ̃ δ̃_t (1 − δ̃_t) dW_t`, `δ̃_0 = δ₀`, with continuous paths in `[0, 1]`.
Araman & Caldentey, *Diffusion Approximations for a Class of Sequential Testing Problems*, arXiv:2102.07030v3, display (12), p.17; the paper takes this solution as given (Proposition 2, p.15,
"`δ̃_t` is a diffusion process solution of the SDE").

**Formalization Note** This keeps the value function of (12) (`IsValueFunction`) from being
vacuous. The probability space lives in `Type`, as in `IsValueFunction`. -/
theorem eq_12_exists (σ : ℝ) (hσ : 0 < σ) (δ₀ : ℝ) (hδ₀ : δ₀ ∈ Icc (0 : ℝ) 1) :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (ℱ : Filtration ℝ≥0 mΩ)
      (B X : ℝ≥0 → Ω → ℝ), IsBeliefDiffusion σ δ₀ P ℱ B X := by sorry

end SeqExpDiffusion
