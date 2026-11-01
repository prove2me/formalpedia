-- Prove2me | Theorems.Thm_SelfGuidedALP_theorem_2
-- name    : SelfGuidedALP.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:30:07.481578+00:00
-- url     : https://prove2.me/theorems/d4da6d0f-9df3-4cce-b38c-e4229d8110ca
-- title:
--   Theorem 2, p.19 (corrected: $(2,\rho)$-norm with square root; $\mathcal W(\Phi)$ without $V\in\mathcal R$) — $H$ further bases give a feasible VFA within $E_{(N,H)}$ of $V^*$
-- statement:
--   Consider a discounted-cost MDP with value function $V^*$ and a class of random basis functions satisfying Assumption 2, with $\rho(\theta)\ge\underline\rho>0$ for all $\theta\in\Theta$. Let $(\beta_0^*,B^*)$ be a representation of $V^*$, let $\delta\in(0,1]$ and $N,H\ge1$, let $\theta^1,\dots,\theta^N\in\Theta$, and let $\beta^{\mathrm{SG}}\in\mathbb R^{N+1}$ be feasible to the constraints (8) for these bases. Put
--   $$
--   E_{(N,H)}:=\frac{2\|B^{*,\perp}_N/\rho\|_{2,\rho}}{(1-\gamma)\,\underline\rho\,\sqrt H}\Bigl(\Omega+2\sqrt{2\ln(1/\delta)}\Bigr).
--   $$
--   Then, with probability at least $1-\delta$ over $H$ iid samples $\theta^{N+1},\dots,\theta^{N+H}$ from $\rho$, there is $\beta\in\mathbb R^{N+H+1}$ such that, for the $N+H$ bases,
--
--   1. $\beta$ is feasible to the constraints (8);
--   2. $\beta$ is $E_{(N,H)}$-feasible to the constraints (9): $V(s;\beta)+E_{(N,H)}\ge V(s;\beta^{\mathrm{SG}})$ for all $s\in\mathcal S$;
--   3. $\|V^*-V(\beta)\|_\infty\le E_{(N,H)}$.
--
--   This is the error bound for the self-guided sequence: after a further $H$ samples the span contains a VFA that is feasible for FALP, nearly feasible for the guiding constraints, and uniformly close to $V^*$, at the dimension-free rate $1/\sqrt H$.
--
--   **Formalization Note** Under the printed Definition EC.2, $B^{*,\perp}_N=B^*$ (the mission's verification file proves it), so $E_{(N,H)}$ does not depend on $N$. The statement keeps the printed construction. The only printed proof of the underlying Proposition EC.1 has a gap; the description explains it.
--
--   Differences from the source:
--   - correction: ‖B/ρ‖_{2,ρ} := ∫_Θ B²/ρ dθ, printed without a square root (p.9), in the bound → the norm of ℬ, (∫_Θ B²/ρ dθ)^{1/2}; reason: the printed bound is quadratic in B and the error is linear: with S = [0,1], one action, P = δ₀, γ = 1/2, ϕ = sin, ρ ≡ 1/4 on [−1,1]², f(s) = ∫θ₁ sin(θ₀+θ₁s)dθ, V* = t·f and B* = tθ₁, the claim forces t·D ≤ t²K with D > 0 for every sample, which fails for small t
--   - correction: a function in W(Φ_N ∪ Φ_H), where W(Φ_N) requires V ∈ 𝓡 (p.19) → any β ∈ ℝ^{N+H+1}, with V(β) the sampled VFA; reason: with S = [0,1], P = δ₀, ϕ = sin, ρ ≡ 1/4 on [−1,1]², every element of 𝓡 is entire and tends to a constant at ±∞ (Riemann–Lebesgue), so a finite combination of sines in 𝓡 is constant, and (iii) fails for V* non-constant once E_(N,H) is small; the proof only checks that β is finite (p.ec10)
--   - reading: there exists a function with vector β such that with a probability of at least 1 − δ → a measurable event of mass ≥ 1 − δ on which coefficients exist, chosen after sampling; reason: the coefficients multiply bases that do not exist before sampling, and the proof chooses them after sampling
--   - reading: given N ≥ 1, for any H ≥ 1; randomness unspecified → every θ¹,…,θᴺ ∈ Θ, probability over the H new samples; reason: Φ_N and β^SG_N are already computed and the proof uses Proposition EC.1 on the H new samples only; this implies the joint-sample statement
--   - reading: a E(N,H)-feasible solution to constraints (9) (not defined) → V(s;β^SG) ≤ V(s;β) + E_(N,H) for all s ∈ S; reason: that is what part (ii) of the proof shows (p.ec11)
--   - encoding: V* := PC(·,π*) for an optimal stationary policy (Assumption 1, p.7) → V is continuous on S and solves the Bellman optimality equation with the minimum attained; reason: the paper uses V* only through this equation (p.8, p.ec2); with γ < 1 its continuous solution is unique, and it is the optimal value under Assumption EC.1
--   - generalization: β^SG_N, Algorithm 2's iterate; Assumption EC.1 and the existence of π* → β^SG any vector feasible to (8); those assumptions dropped; reason: the proof uses β^SG_N only through V(β^SG_N) ≤ V*, and Algorithm 2's iterate is (8)-feasible; a paper instance satisfies the Lean hypotheses
--   - encoding: ρ(θ) ≥ ρ̲; action sets compact or finite; B* a function with finite (2,ρ)-norm → 0 < ρ̲; A s compact; B* an element of the L² space ℬ; reason: the bound divides by ρ̲ and p.11 presents the condition as keeping ρ away from zero; finite sets are compact; finiteness of the norm is the type of B*
--   - reading: (β*₀,B*) an optimal solution to FELP (associated to V*) → every representation (β*₀,B*) of V* with B* ∈ ℬ; reason: the proofs use only V* = V(·;(β*₀,B*)); a FELP optimum that does not represent V* (say ν a point mass) would break (EC.12), and every representation is FELP-optimal by the proof of Proposition 1
--   - reading: integrals dθ with a sampling density ρ(θ) on Θ ⊆ ℝ^{d+1} → dθ is Lebesgue measure on ℝ^{d+1} and ρ a density for it; reason: the paper never names another reference measure, and its Definition EC.2 calls ℬ an L² space; laws without a Lebesgue density (Table 1's sphere and stump, p.8) are outside this reading
-- source:
--   Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, Theorem 2, p.19

import Mathlib
import Definitions.Def_SelfGuidedALP_Assumption2
import Definitions.Def_SelfGuidedALP_IsOptimalValue
import Definitions.Def_SelfGuidedALP_FALPFeasible
import Definitions.Def_SelfGuidedALP_iidLaw
import Definitions.Def_SelfGuidedALP_vfa
import Definitions.Def_SelfGuidedALP_perpPart
import Definitions.Def_SelfGuidedALP_EConst
import Definitions.Def_SelfGuidedALP_WithProbAtLeast

open MeasureTheory

namespace SelfGuidedALP

/-- Theorem 2 of Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, p.19, with the `(2,ρ)`-norm taken with its square root and with
`𝒲(Φ_N ∪ Φ_H)` the span of `1` and the sampled bases. Fix `θ¹, …, θᴺ ∈ Θ`, a vector `βSG ∈ ℝ^{N+1}`
feasible to (8) and a representation `(β*₀, B*)` of `V*`. With probability at least `1 − δ` over `H`
further iid samples from `ρ`, there is `β ∈ ℝ^{N+H+1}`, chosen after sampling, which (i) is feasible
to the constraints (8) for the `N + H` bases, (ii) satisfies the constraints (9) relaxed by
`E_(N,H)`, and (iii) satisfies `‖V* − V(β)‖_∞ ≤ E_(N,H)`. -/
theorem theorem_2 {d m N H : ℕ} (M : MDP d m) (R : RBClass d) (L : ℝ)
    (Vstar : EuclideanSpace ℝ (Fin d) → ℝ) (hVstar : IsOptimalValue M Vstar)
    (hA2 : Assumption2 M R L Vstar) (ρlow : ℝ) (hρlow : 0 < ρlow)
    (hρ : ∀ θ ∈ R.Θ, ρlow ≤ R.ρ θ) (βs : ℝ) (Bs : Bspace R) (hrep : IsRep M R Vstar βs Bs)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hN : 1 ≤ N) (hH : 1 ≤ H)
    (θN : Fin N → EuclideanSpace ℝ (Fin (d + 1))) (hθN : ∀ i, θN i ∈ R.Θ)
    (βSG : Fin (N + 1) → ℝ) (hβSG : FALPFeasible M R θN βSG) :
    WithProbAtLeast (iidLaw R H) (1 - δ) fun ω =>
      ∃ β : Fin (N + H + 1) → ℝ,
        FALPFeasible M R (Fin.append θN ω) β ∧
          (∀ s ∈ M.S, vfa R θN βSG s ≤
            vfa R (Fin.append θN ω) β s + EConst M R L ρlow δ H (perpPart R θN Bs)) ∧
          ∀ s ∈ M.S, |Vstar s - vfa R (Fin.append θN ω) β s| ≤
            EConst M R L ρlow δ H (perpPart R θN Bs) := by sorry

end SelfGuidedALP
