-- Prove2me | Theorems.Thm_StrategicObfuscation_effort_monotone
-- name    : StrategicObfuscation.effort_monotone
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:51:59.021458+00:00
-- url     : https://prove2.me/theorems/54055d09-5dcb-4ba6-9546-f27ac4086866
-- title:
--   §3, p.10 — best-response effort vanishes at $\alpha=0$ or $g=0$ and increases in $\alpha$, $\sigma$ and $g$
-- statement:
--   Let $\pi$ be a detection probability, $g>0$ and $e(\alpha,\sigma)$ an effort selection. Then, for $\alpha,\alpha',\sigma,\sigma'\in[0,1]$:
--
--   1. $e(0,\sigma)=0$, and at return $0$ the only best response is $0$;
--   2. if $\alpha<\alpha'$ then $e(\alpha,\sigma)\le e(\alpha',\sigma)$;
--   3. if $\sigma<\sigma'$ then $e(\alpha,\sigma)\le e(\alpha,\sigma')$;
--   4. if $0\le g_1<g_2$, every best response at return $g_1$ is at most every best response at return $g_2$.
--
--   These comparative statics drive the whole analysis: funding uncertified proposals and giving reviewers more resources both raise the return from obfuscation.
--
--   Differences from the source:
--   - generalization: Assumption 1 with ∂²π/∂σ∂e < 0 for a twice differentiable π → IsDetection: monotonicity plus decreasing differences in σ, strict whenever π(σ,·) separates the two efforts; reason: the C² class satisfies it by integrating the mixed partial, and the paper's own example on p.14, which the strict form excludes, also satisfies it
--   - encoding: e(α, σ) written as a function → a fixed selection E with IsEffort π g E; reason: the argmax in (1) may not be a singleton; every selection is covered and existence of a maximizer stays part of the hypothesis, as in (1)
--   - reading: effort "increases" with α, g and σ → weak inequalities; reason: strict increase is false, since effort stays at 0 on a range of parameters, as Figure 3 shows
-- source:
--   Figueroa & Lemus, The Benefit of the Doubt: Decision Making under Strategic Obfuscation, SSRN 3840423 (version of April 4, 2022), §3, p.10

import Mathlib
import Definitions.Def_StrategicObfuscation_IsDetection
import Definitions.Def_StrategicObfuscation_IsEffort

open Set

namespace StrategicObfuscation

/-- **Best-response effort is zero at `α = 0` or `g = 0` and increases in `α`, `σ` and `g`.**
Figueroa & Lemus, *The Benefit of the Doubt: Decision Making under Strategic Obfuscation*,
SSRN 3840423 (version of April 4, 2022), §3, p.10 (PDF p.10): "Clearly, e(0, σ, g) = e(α, σ, 0) = 0,
and the applicant's obfuscation effort increases with α and g. … Assumption 1 implies that the
return from obfuscation is higher when applicants face more resourceful reviewers, i.e., e is
increasing in σ."

**Formalization Note** "Increases" is weak, as it must be: effort stays at `0` on a range of `α` and
`σ`. Monotonicity in `α` and `σ` is stated for the selection `E`, and it holds for any selection.
Monotonicity in `g` is stated for arbitrary best responses at the two returns. -/
theorem effort_monotone {g : ℝ} {π : ℝ → ℝ → ℝ} {E : ℝ → ℝ → ℝ}
    (hg : 0 < g) (hπ : IsDetection π) (hE : IsEffort π g E) :
    (∀ σ ∈ Icc (0 : ℝ) 1, E 0 σ = 0) ∧
    (∀ α ∈ Icc (0 : ℝ) 1, ∀ σ ∈ Icc (0 : ℝ) 1, ∀ e, IsBestResponse π 0 α σ e → e = 0) ∧
    (∀ α ∈ Icc (0 : ℝ) 1, ∀ α' ∈ Icc (0 : ℝ) 1, α < α' →
      ∀ σ ∈ Icc (0 : ℝ) 1, E α σ ≤ E α' σ) ∧
    (∀ α ∈ Icc (0 : ℝ) 1, ∀ σ ∈ Icc (0 : ℝ) 1, ∀ σ' ∈ Icc (0 : ℝ) 1, σ < σ' →
      E α σ ≤ E α σ') ∧
    (∀ g₁ g₂ : ℝ, 0 ≤ g₁ → g₁ < g₂ → ∀ α ∈ Icc (0 : ℝ) 1, ∀ σ ∈ Icc (0 : ℝ) 1, ∀ e₁ e₂,
      IsBestResponse π g₁ α σ e₁ → IsBestResponse π g₂ α σ e₂ → e₁ ≤ e₂) := by sorry

end StrategicObfuscation
