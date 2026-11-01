-- Prove2me | Theorems.Thm_SelfGuidedALP_proposition_EC_1
-- name    : SelfGuidedALP.proposition_EC_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:29:42.223809+00:00
-- url     : https://prove2.me/theorems/ac2db0ba-e513-41e4-baea-e6ae1ea3f849
-- title:
--   Proposition EC.1, p.ec2 (corrected: $(2,\rho)$-norm with square root) — $N$ random bases approximate $V(\boldsymbol\beta)$ at rate $1/\sqrt N$
-- statement:
--   Suppose $\rho(\theta)\ge\underline\rho>0$ for all $\theta\in\Theta$ and Assumption 2 holds. Let $\delta\in(0,1]$, $N\ge1$, and $V(s;\boldsymbol\beta)=\beta_0+\int_\Theta B(\theta)\varphi(s;\theta)\,\mathrm d\theta$ with $\|B/\rho\|_{2,\rho}<\infty$. Then, with probability at least $1-\delta$ over $N$ iid samples $\theta^1,\dots,\theta^N$ from $\rho$, there are finite coefficients $\bar\beta_0,\dots,\bar\beta_N$ with
--   $$
--   \Bigl\|V(\boldsymbol\beta)-\Bigl(\bar\beta_0+\sum_{i=1}^N\bar\beta_i\varphi(\cdot;\theta^i)\Bigr)\Bigr\|_\infty\le\frac{\|B/\rho\|_{2,\rho}}{\underline\rho\sqrt N}\Bigl(\Omega+\sqrt{2\ln(1/\delta)}\Bigr).
--   $$
--
--   This is the sup-norm random-feature approximation bound that all the probabilistic statements of the mission rest on.
--
--   Differences from the source:
--   - correction: ‖B/ρ‖_{2,ρ} := ∫_Θ B²/ρ dθ, printed without a square root (p.9), in the bound → the norm of ℬ, (∫_Θ B²/ρ dθ)^{1/2}; reason: the printed bound is quadratic in B and the error is linear: with S = [0,1], one action, P = δ₀, γ = 1/2, ϕ = sin, ρ ≡ 1/4 on [−1,1]², f(s) = ∫θ₁ sin(θ₀+θ₁s)dθ, V* = t·f and B* = tθ₁, the claim forces t·D ≤ t²K with D > 0 for every sample, which fails for small t
--   - reading: there exist coefficients such that with a probability of at least 1 − δ → a measurable event of mass ≥ 1 − δ on which coefficients exist, chosen after sampling; reason: the coefficients multiply bases that do not exist before sampling, and the proof chooses them after sampling
--   - encoding: ρ(θ) ≥ ρ̲ for all θ ∈ Θ → the same, plus 0 < ρ̲; reason: the bound divides by ρ̲, and p.11 presents the condition as keeping ρ away from zero
--   - encoding: N iid samples, with √N in the denominator → 1 ≤ N; reason: N = 0 would divide by zero; the source's N is a positive sample count
--   - encoding: V* := PC(·,π*) for an optimal stationary policy (Assumption 1, p.7) → V is continuous on S and solves the Bellman optimality equation with the minimum attained; reason: the paper uses V* only through this equation (p.8, p.ec2); with γ < 1 its continuous solution is unique, and it is the optimal value under Assumption EC.1
--   - generalization: Assumption EC.1 and the existence of π* (pp.7, ec1) → dropped: no boundedness, semicontinuity or kernel continuity is assumed; reason: those conditions only guarantee that V* exists and solves the Bellman equation, which is now a hypothesis; a paper instance satisfies the Lean hypotheses
--   - encoding: each action set is continuous compact or finite → each A s is a nonempty compact subset of ℝᵐ; reason: a finite set is compact, so both cases are covered
--   - reading: integrals dθ with a sampling density ρ(θ) on Θ ⊆ ℝ^{d+1} → dθ is Lebesgue measure on ℝ^{d+1} and ρ a density for it; reason: the paper never names another reference measure, and its Definition EC.2 calls ℬ an L² space; laws without a Lebesgue density (Table 1's sphere and stump, p.8) are outside this reading
-- source:
--   Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, Proposition EC.1, eq. (EC.1), p.ec2

import Mathlib
import Definitions.Def_SelfGuidedALP_Assumption2
import Definitions.Def_SelfGuidedALP_IsOptimalValue
import Definitions.Def_SelfGuidedALP_iidLaw
import Definitions.Def_SelfGuidedALP_vfa
import Definitions.Def_SelfGuidedALP_Omega
import Definitions.Def_SelfGuidedALP_WithProbAtLeast

open MeasureTheory

namespace SelfGuidedALP

/-- Proposition EC.1 of Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, eq. (EC.1), p.ec2, with the square-root norm: with probability at
least `1 − δ` over `N` iid samples from `ρ`, some coefficients `β̄ ∈ ℝ^{N+1}`, chosen after sampling,
satisfy `‖V(𝛃) − (β̄₀ + ∑ᵢ β̄ᵢ ϕ(·;θⁱ))‖_∞ ≤ ‖B/ρ‖_{2,ρ}/(ρ̲ √N) · (Ω + √(2 ln(1/δ)))`. -/
theorem proposition_EC_1 {d m : ℕ} (M : MDP d m) (R : RBClass d) (L : ℝ)
    (Vstar : EuclideanSpace ℝ (Fin d) → ℝ) (hVstar : IsOptimalValue M Vstar)
    (hA2 : Assumption2 M R L Vstar) (ρlow : ℝ) (hρlow : 0 < ρlow)
    (hρ : ∀ θ ∈ R.Θ, ρlow ≤ R.ρ θ) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (β₀ : ℝ) (B : Bspace R) (N : ℕ) (hN : 1 ≤ N) :
    WithProbAtLeast (iidLaw R N) (1 - δ) fun ω =>
      ∃ βbar : Fin (N + 1) → ℝ, ∀ s ∈ M.S,
        |intVFA R β₀ B s - vfa R ω βbar s| ≤
          ‖B‖ / (ρlow * Real.sqrt N) *
            (Omega M R L + Real.sqrt (2 * Real.log (1 / δ))) := by sorry

end SelfGuidedALP
