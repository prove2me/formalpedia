-- Prove2me | Theorems.Thm_SeqExpDiffusion_theorem_1
-- name    : SeqExpDiffusion.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:11:04.213803+00:00
-- url     : https://prove2.me/theorems/e915db56-b86e-4f9f-b288-be055e05023c
-- title:
--   Theorem 1 (Verification) — a QVI solution dominates the value, with equality for a QVI-control of finite mean (corrected: squared ℋ)
-- statement:
--   Let $r>0$, $\tilde\sigma>0$ and let $H$ be a payoff continuous on $[0,1]$. Let $f\in\widehat{\mathcal C}^2$ solve the quasi-variational inequalities (15) for $H$. Then
--
--   1. $f(\delta)\ge\tilde{\mathcal G}(\delta)$ for every $\delta\in[0,1]$: for every belief diffusion $\tilde\delta$ started at $\delta$ and every stopping time $\tau$,
--   $$\mathbb E\big[e^{-r\tau}H(\tilde\delta_\tau)\big]\le f(\delta);$$
--   2. if a QVI-control $\tau=\inf\{t>0: f(\tilde\delta_t)=H(\tilde\delta_t)\}$ associated with $f$ is a stopping time with $\mathbb E[\tau]<\infty$, then $\tau$ is optimal and $f(\delta)=\tilde{\mathcal G}(\delta)$: its expected reward equals $f(\delta)$, and $f(\delta)$ is the least upper bound of all expected rewards.
--
--   This theorem reduces the computation of the value to solving the QVI; it is how the closed forms of Proposition 5 and the pairwise maximum of Theorem 2 are identified as values.
--
--   **Formalization Note** $\inf\emptyset=\infty$, and the reward on $\{\tau=\infty\}$ is $0$. The filtration need not be right-continuous, so the QVI-control is assumed to be a stopping time. No sign condition on $f$ is assumed.
--
--   Differences from the source:
--   - correction: ℋf = ½ σ̃ δ(1−δ) f″ − r f (display (14), p.18) → ℋf = ½ (σ̃ δ(1−δ))² f″ − r f; reason: the printed operator is not the generator of (12); e.g. for σ̃ = 2, r = 1 the closed form (18) does not solve the printed ℋu = 0 (the ratio δ(1−δ)φ₁″/φ₁ of φ₁ = (1−δ)^{1−γ}δ^γ is 2.38 at δ = 0.3 and 2.08 at δ = 0.6), while it solves the squared one; the page itself uses the square on pp.19, 50, 52
--   - generalization: the payoff G of (1) → any payoff H continuous on [0, 1]; reason: G is continuous on [0, 1], and so is each two-action payoff G̃_ij
--   - generalization: stopping times of the filtration 𝔽 of the experimentation history (p.8) → every probability space and every filtration for which the driving motion is Brownian; reason: the paper's setting is one instance, so the statement specializes to it
--   - reading: the QVI-control τ = inf{t > 0 : f(δ̃_t) = G(δ̃_t)} is a stopping time (Definition 4, "for every solution … we can associate a control τ ∈ 𝕋") → τ is assumed to be a stopping time equal to the printed infimum; reason: with a filtration that is not right-continuous the infimum need not be a stopping time; the page places it in 𝕋
--   - reading: (12) is silent on the event τ = ∞ → the reward is 0 on {τ = ∞}; reason: the payoffs are bounded, so this changes no supremum relative to finite stopping times
--   - encoding: the value 𝒢̃ = sup over stopping times of a solution of (12) → least upper bound over [0, ∞]-valued stopping times, for every solution with continuous paths in [0, 1] and the published Itô relation; reason: Lean conventions; the supremum is never a default value
--   - encoding: r and σ̃ are a discount rate and a volatility, with no stated sign → r > 0 and σ̃ > 0; reason: the paper uses both silently (γ needs σ̃ ≠ 0, and r = 0 gives γ = 1); only degenerate cases are excluded
-- source:
--   Araman & Caldentey, Diffusion Approximations for a Class of Sequential Testing Problems, arXiv:2102.07030v3, Theorem 1, p.18; Definitions 3 and 4, p.18

import Definitions.Def_SeqExpDiffusion_IsBeliefDiffusion
import Definitions.Def_SeqExpDiffusion_rewardSet
import Definitions.Def_SeqExpDiffusion_SolvesQVI
import Definitions.Def_TechBreakthrough_discountedAt

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace SeqExpDiffusion

/-- Theorem 1 (Verification), Araman & Caldentey, *Diffusion Approximations for a Class of Sequential Testing Problems*, arXiv:2102.07030v3, p.18: let `f ∈ Ĉ²` solve the QVI (15). Then
`f(δ) ≥ 𝒢̃(δ)` for every `δ ∈ [0, 1]`. In addition, if there exists a QVI-control `τ` associated with
`f` (Definition 4, p.18: `τ = inf{t > 0 : f(δ̃_t) = G(δ̃_t)}`) such that `E[τ] < ∞`, then `τ` is
optimal and `f(δ) = 𝒢̃(δ)`.

**Formalization Note** `𝒢̃(δ)` is the least upper bound of the expected rewards over stopping times
for any solution of (12) started at `δ`, so the first clause says that `f δ` bounds them all. The
payoff is any `H` continuous on `[0, 1]` (the paper's `G` of (1) is one, and so is each two-action
payoff `G̃_ij`). `ℋ` is the corrected operator (14). The filtration need not be right-continuous, so
the QVI-control is taken as a stopping time equal to the printed infimum (`inf ∅ = ∞`). No sign
condition on `f` is assumed. -/
theorem theorem_1 (r σ : ℝ) (hr : 0 < r) (hσ : 0 < σ) (H f : ℝ → ℝ)
    (hH : ContinuousOn H (Icc 0 1)) (hf : SolvesQVI r σ H f) :
    (∀ δ ∈ Icc (0 : ℝ) 1, ∀ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (ℱ : Filtration ℝ≥0 mΩ)
        (B X : ℝ≥0 → Ω → ℝ), IsBeliefDiffusion σ δ P ℱ B X →
        f δ ∈ upperBounds (rewardSet r H P ℱ X)) ∧
    (∀ δ ∈ Icc (0 : ℝ) 1, ∀ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (ℱ : Filtration ℝ≥0 mΩ)
        (B X : ℝ≥0 → Ω → ℝ), IsBeliefDiffusion σ δ P ℱ B X →
        ∀ τ : Ω → WithTop ℝ≥0, IsStoppingTime ℱ τ →
        (∀ ω, τ ω = TechBreakthrough.firstTime {t | 0 < t ∧ f (X t ω) = H (X t ω)}) →
        ∫⁻ ω, (τ ω : ℝ≥0∞) ∂P < ∞ →
        Integrable (fun ω => TechBreakthrough.discountedAt r (fun t => H (X t ω)) (τ ω)) P ∧
        ∫ ω, TechBreakthrough.discountedAt r (fun t => H (X t ω)) (τ ω) ∂P = f δ ∧
        IsLUB (rewardSet r H P ℱ X) (f δ)) := by sorry

end SeqExpDiffusion
