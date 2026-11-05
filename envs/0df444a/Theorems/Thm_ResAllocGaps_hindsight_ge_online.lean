-- Prove2me | Theorems.Thm_ResAllocGaps_hindsight_ge_online
-- name    : ResAllocGaps.hindsight_ge_online
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:30:14.895894+00:00
-- url     : https://prove2.me/theorems/4ee18954-1f8d-4f83-a3ac-0d362728bd90
-- title:
--   §2, p.9 — the hindsight value dominates every online policy, pathwise and in expectation
-- statement:
--   Let the candidate abilities have a law $\mu$ on $[0,1]$. For every budget $B$, horizon $T$ and feasible online policy $\pi\in\Pi(B,T)$:
--
--   1. almost surely, the policy's reward is at most the hindsight value, $R^\pi_T\le V^{hs}_1(B,T;\theta)$, i.e. $\Lambda(B,T;\pi)\ge0$;
--   2. in expectation,
--   $$V^{hs}_1(B,T)\ \ge\ V^\pi_1(B,T),$$
--   so $\mathrm{Regret}(B,T;\pi)\ge0$.
--
--   The pathwise form is what lets the regret be split over disjoint events in the proof of the lower bound.
--
--   Differences from the source:
--   - generalization: V^hs_1(B, T) ≥ V^π_1(B, T) → the same, and also R^π_T ≤ V^hs_1(B, T; θ) almost surely; reason: the expectation form is the second clause; the pathwise clause is extra
--   - generalization: ∀ B ∈ [T] → every B ∈ ℕ; reason: specializes to B ∈ [T]
--   - encoding: candidate abilities drawn from a distribution F on [0, 1] → a probability measure μ on ℝ with μ([0, 1]) = 1; reason: the paper's standing assumption on abilities (abstract; p.10–11); same distributions
--   - encoding: times t = 1, …, T; requests θ_t and seeds U_t; actions in {reject, accept}; Π(B, T) of p.8 → index t − 1 : Fin T; sample Fin T → ℝ × ℝ with law (μ ⊗ Unif[0,1])^{⊗T}; accept bits (Bool) measurable in the observed prefix; at most B acceptances almost surely (OnlinePolicy); reason: Lean convention; by Doob–Dynkin these are exactly the 𝓕_t-measurable actions of p.8, so the same policies
-- source:
--   O. Besbes, Y. Kanoria and A. Kumar, Dynamic Resource Allocation: Algorithmic Design Principles and Spectrum of Achievable Performances, arXiv:2205.09078v2 (6 Oct 2023), https://arxiv.org/abs/2205.09078v2, §2, p.9 ('It trivially follows that …')

import Mathlib
import Definitions.Def_ResAllocGaps_OnlinePolicy

open MeasureTheory

namespace ResAllocGaps

/-- **The hindsight dominates every online policy**, Besbes, Kanoria & Kumar, arXiv:2205.09078v2,
§2, p.9: "It trivially follows that `V^hs_1(B, T) ≥ V^π_1(B, T)`, `∀π ∈ Π(B, T)` and `∀B ∈ [T]`",
here for the multisecretary problem, together with its pathwise form: almost surely the policy's
reward is at most the hindsight value, i.e. `Λ(B, T; π) ≥ 0` a.s.

**Formalization Note.** The ability law `μ` is a probability measure with `μ([0, 1]) = 1`; `B` is
any natural number. -/
theorem hindsight_ge_online (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Set.Icc 0 1) = 1)
    (T B : ℕ) (π : OnlinePolicy μ T B) :
    (∀ᵐ ω ∂(sampleLaw μ T), π.reward ω ≤ hsValue T B (abilities ω)) ∧
      ∫ ω, π.reward ω ∂(sampleLaw μ T) ≤ ∫ ω, hsValue T B (abilities ω) ∂(sampleLaw μ T) := by sorry

end ResAllocGaps
