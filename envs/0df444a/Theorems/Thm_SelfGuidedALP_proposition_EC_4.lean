-- Prove2me | Theorems.Thm_SelfGuidedALP_proposition_EC_4
-- name    : SelfGuidedALP.proposition_EC_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:29:30.458934+00:00
-- url     : https://prove2.me/theorems/25fb42fd-d95b-40a4-80a7-f1878fd2f6fa
-- title:
--   Proposition EC.4, p.ec9 (corrected: $(2,\rho)$-norm with square root) — $H$ further bases give $\tilde\beta$ within $\zeta+O(1/\sqrt H)$ of $V^*$
-- statement:
--   Suppose $\rho(\theta)\ge\underline\rho>0$ on $\Theta$. Let $\zeta>0$, $\delta\in(0,1]$, $H\ge1$, let $(\beta_0^*,B^*)$ represent $V^*$ with $B^*=B^{*,o}_N+B^{*,\perp}_N$ as in Proposition EC.3, and let $B^\zeta_N$, $(\beta^\zeta_1,\dots,\beta^\zeta_N)$ be as described there. Then, with probability at least $1-\delta$ over $H$ iid samples $\theta^{N+1},\dots,\theta^{N+H}$ from $\rho$, there are $(\beta^\perp_0,\beta^\perp_{N+1},\dots,\beta^\perp_{N+H})$ such that $\tilde\beta:=(\beta_0^*+\beta_0^\perp,\beta^\zeta_1,\dots,\beta^\zeta_N,\beta^\perp_{N+1},\dots,\beta^\perp_{N+H})\in\mathbb R^{N+H+1}$ satisfies
--   $$
--   \|V^*-V(\tilde\beta)\|_\infty\le\zeta+\frac{\|B^{*,\perp}_N/\rho\|_{2,\rho}}{\underline\rho\sqrt H}\Bigl(\Omega+\sqrt{2\ln(1/\delta)}\Bigr).
--   $$
--
--   This keeps the old weights and fits only the orthogonal part with the new bases.
--
--   Differences from the source:
--   - correction: ‖B/ρ‖_{2,ρ} := ∫_Θ B²/ρ dθ, printed without a square root (p.9), in the bound → the norm of ℬ, (∫_Θ B²/ρ dθ)^{1/2}; reason: the printed bound is quadratic in B and the error is linear: with S = [0,1], one action, P = δ₀, γ = 1/2, ϕ = sin, ρ ≡ 1/4 on [−1,1]², f(s) = ∫θ₁ sin(θ₀+θ₁s)dθ, V* = t·f and B* = tθ₁, the claim forces t·D ≤ t²K with D > 0 for every sample, which fails for small t
--   - reading: there exist coefficients such that with a probability of at least 1 − δ → a measurable event of mass ≥ 1 − δ on which coefficients exist, chosen after sampling; reason: the coefficients multiply bases that do not exist before sampling, and the proof chooses them after sampling
--   - reading: N and then H iid samples → every θ¹,…,θᴺ ∈ Θ, probability over the H new samples; reason: the proof applies Proposition EC.1 to the H new samples only; this implies the joint-sample statement
--   - reading: (β*₀,B*) an optimal solution to FELP (associated to V*) → every representation (β*₀,B*) of V* with B* ∈ ℬ; reason: the proofs use only V* = V(·;(β*₀,B*)); a FELP optimum that does not represent V* (say ν a point mass) would break (EC.12), and every representation is FELP-optimal by the proof of Proposition 1
--   - reading: the coefficients described in Proposition EC.3 → any B^ζ_N ∈ ℬ_N and β^ζ satisfying the two conclusions of Proposition EC.3 for this ζ; reason: the proof uses only those two conclusions
--   - encoding: (β^⊥₀,β^⊥_{N+1},…,β^⊥_{N+H}) ∈ ℝ^H → H + 1 entries; reason: the printed exponent is a typo: the tuple has H + 1 entries and the proof writes ℝ^{H+1} (EC.14)
--   - encoding: ρ(θ) ≥ ρ̲ for all θ ∈ Θ → the same, plus 0 < ρ̲; reason: the bound divides by ρ̲, and p.11 presents the condition as keeping ρ away from zero
--   - encoding: V* := PC(·,π*) for an optimal stationary policy (Assumption 1, p.7) → V is continuous on S and solves the Bellman optimality equation with the minimum attained; reason: the paper uses V* only through this equation (p.8, p.ec2); with γ < 1 its continuous solution is unique, and it is the optimal value under Assumption EC.1
--   - generalization: Assumption EC.1 and the existence of π* (pp.7, ec1) → dropped: no boundedness, semicontinuity or kernel continuity is assumed; reason: those conditions only guarantee that V* exists and solves the Bellman equation, which is now a hypothesis; a paper instance satisfies the Lean hypotheses
--   - encoding: each action set is continuous compact or finite → each A s is a nonempty compact subset of ℝᵐ; reason: a finite set is compact, so both cases are covered
--   - reading: integrals dθ with a sampling density ρ(θ) on Θ ⊆ ℝ^{d+1} → dθ is Lebesgue measure on ℝ^{d+1} and ρ a density for it; reason: the paper never names another reference measure, and its Definition EC.2 calls ℬ an L² space; laws without a Lebesgue density (Table 1's sphere and stump, p.8) are outside this reading
-- source:
--   Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, Proposition EC.4, p.ec9

import Mathlib
import Definitions.Def_SelfGuidedALP_Assumption2
import Definitions.Def_SelfGuidedALP_IsOptimalValue
import Definitions.Def_SelfGuidedALP_BNbar
import Definitions.Def_SelfGuidedALP_iidLaw
import Definitions.Def_SelfGuidedALP_vfa
import Definitions.Def_SelfGuidedALP_Omega
import Definitions.Def_SelfGuidedALP_WithProbAtLeast

open MeasureTheory

namespace SelfGuidedALP

/-- Proposition EC.4 of Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, p.ec9, with the square-root norm: given the first `N` bases and
coefficients `β^ζ` as described in Proposition EC.3, with probability at least `1 − δ` over `H`
further iid samples there are `(β^⊥₀, β^⊥_{N+1}, …, β^⊥_{N+H})`, chosen after sampling, such that
`β̃ := (β*₀ + β^⊥₀, β^ζ_1, …, β^ζ_N, β^⊥_{N+1}, …, β^⊥_{N+H})` satisfies
`‖V* − V(β̃)‖_∞ ≤ ζ + ‖B^{*,⊥}_N/ρ‖_{2,ρ}/(ρ̲ √H) · (Ω + √(2 ln(1/δ)))`. -/
theorem proposition_EC_4 {d m N : ℕ} (M : MDP d m) (R : RBClass d) (L : ℝ)
    (Vstar : EuclideanSpace ℝ (Fin d) → ℝ) (hVstar : IsOptimalValue M Vstar)
    (hA2 : Assumption2 M R L Vstar) (ρlow : ℝ) (hρlow : 0 < ρlow)
    (hρ : ∀ θ ∈ R.Θ, ρlow ≤ R.ρ θ) (βs : ℝ) (Bs : Bspace R) (hrep : IsRep M R Vstar βs Bs)
    (θs : Fin N → EuclideanSpace ℝ (Fin (d + 1))) (hθs : ∀ i, θs i ∈ R.Θ)
    (ζ : ℝ) (hζ : 0 < ζ) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (Bo Bp : Bspace R) (hBo : Bo ∈ BNbar R θs) (hBp : Bp ∈ (BNbar R θs)ᗮ) (hdecomp : Bs = Bo + Bp)
    (Bz : Bspace R) (hBz : Bz ∈ BN R θs) (βz : Fin N → ℝ)
    (hbound : ∀ s ∈ M.S, |Vstar s - (intVFA R βs Bz s + intVFA R 0 Bp s)| ≤ ζ)
    (hcoef : ∀ s ∈ M.S, intVFA R βs Bz s = βs + ∑ i, βz i * feat R.ϕ (θs i) s)
    (H : ℕ) (hH : 1 ≤ H) :
    WithProbAtLeast (iidLaw R H) (1 - δ) fun ω =>
      ∃ (βp0 : ℝ) (βpH : Fin H → ℝ), ∀ s ∈ M.S,
        |Vstar s - vfa R (Fin.append θs ω) (Fin.cons (βs + βp0) (Fin.append βz βpH)) s| ≤
          ζ + ‖Bp‖ / (ρlow * Real.sqrt H) *
            (Omega M R L + Real.sqrt (2 * Real.log (1 / δ))) := by sorry

end SelfGuidedALP
