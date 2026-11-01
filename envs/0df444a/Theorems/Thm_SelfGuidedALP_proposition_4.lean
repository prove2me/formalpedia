-- Prove2me | Theorems.Thm_SelfGuidedALP_proposition_4
-- name    : SelfGuidedALP.proposition_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:29:53.812152+00:00
-- url     : https://prove2.me/theorems/fe311172-7413-40e3-b30d-62a092d19482
-- title:
--   Proposition 4, p.18 — Algorithm 2's VFAs increase monotonically and stay below $V^*$
-- statement:
--   Let $\beta^{\mathrm{SG}}_{b},\dots,\beta^{\mathrm{SG}}_{nb}$ be a run of Algorithm 2 with batch size $b\ge1$, for an integer $n\ge1$. Then $\beta^{\mathrm{SG}}_{b}$ is an optimal solution of $\mathrm{FALP}_b$, and
--   $$
--   V(s;\beta^{\mathrm{SG}}_{b})\le V(s;\beta^{\mathrm{SG}}_{2b})\le\cdots\le V(s;\beta^{\mathrm{SG}}_{nb})\le V^*(s)\qquad\text{for all }s\in\mathcal S .
--   $$
--
--   The guiding constraints thus produce VFAs that approach $V^*$ state by state, so the sup-norm and $(1,\mu)$-norm distances to $V^*$ do not increase along the run.
--
--   Differences from the source:
--   - reading: V(s;β^FA_b) = V(s;β^SG_b), with β^FA_b any optimal FALP_b solution → β^SG_b is an optimal solution of FALP_b; reason: the equality is false for two different optimal solutions (S = [0,1], one action, P = δ₀, c ≡ 0, ν = δ₀, θ¹ = (0,1): every (0,β₁) with β₁ ≤ 0 is optimal), and the paper's justification is that the first iteration is FALP_b
--   - reading: the iterates of Algorithm 2 on iid draws → any sample stream in Θ with iterates optimal for that stream; reason: the claim is about one realization and has no probability; existence of each iterate (Assumption 3) is part of the run hypothesis
--   - encoding: V* := PC(·,π*) for an optimal stationary policy (Assumption 1, p.7) → V is continuous on S and solves the Bellman optimality equation with the minimum attained; reason: the paper uses V* only through this equation (p.8, p.ec2); with γ < 1 its continuous solution is unique, and it is the optimal value under Assumption EC.1
--   - generalization: Assumption EC.1 and the existence of π* (pp.7, ec1) → dropped: no boundedness, semicontinuity or kernel continuity is assumed; reason: those conditions only guarantee that V* exists and solves the Bellman equation, which is now a hypothesis; a paper instance satisfies the Lean hypotheses
--   - encoding: each action set is continuous compact or finite → each A s is a nonempty compact subset of ℝᵐ; reason: a finite set is compact, so both cases are covered
--   - reading: integrals dθ with a sampling density ρ(θ) on Θ ⊆ ℝ^{d+1} → dθ is Lebesgue measure on ℝ^{d+1} and ρ a density for it; reason: the paper never names another reference measure, and its Definition EC.2 calls ℬ an L² space; laws without a Lebesgue density (Table 1's sphere and stump, p.8) are outside this reading
-- source:
--   Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, Proposition 4, eq. (10), p.18

import Mathlib
import Definitions.Def_SelfGuidedALP_Assumption2
import Definitions.Def_SelfGuidedALP_IsOptimalValue
import Definitions.Def_SelfGuidedALP_IsAlgorithm2Run
import Definitions.Def_SelfGuidedALP_IsStateRelevance

open MeasureTheory

namespace SelfGuidedALP

/-- Proposition 4 of Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, eq. (10), p.18: along a run of Algorithm 2, `β^SG_b` is the `FALP_b`
solution (the equality `V(s;β^FA_b) = V(s;β^SG_b)`), and
`V(s;β^SG_b) ≤ V(s;β^SG_{2b}) ≤ ⋯ ≤ V(s;β^SG_{nb}) ≤ V*(s)` for all `s ∈ 𝒮`. -/
theorem proposition_4 {d m : ℕ} (M : MDP d m) (R : RBClass d) (L : ℝ)
    (Vstar : EuclideanSpace ℝ (Fin d) → ℝ) (hVstar : IsOptimalValue M Vstar)
    (hA2 : Assumption2 M R L Vstar) (ν₀ : Measure (EuclideanSpace ℝ (Fin d))) (hν₀ : IsStateRelevance M ν₀)
    (b : ℕ) (hb : 1 ≤ b) (θ : ℕ → EuclideanSpace ℝ (Fin (d + 1))) (hθ : ∀ i, θ i ∈ R.Θ)
    (n : ℕ) (hn : 1 ≤ n) (iter : (k : ℕ) → Fin (k * b + 1) → ℝ)
    (hrun : IsAlgorithm2Run M R ν₀ θ b n iter) :
    IsFALPOptimal M R ν₀ (fun i : Fin (1 * b) => θ i) (iter 1) ∧
      (∀ k, 1 ≤ k → k < n → ∀ s ∈ M.S,
        vfa R (fun i : Fin (k * b) => θ i) (iter k) s ≤
          vfa R (fun i : Fin ((k + 1) * b) => θ i) (iter (k + 1)) s) ∧
      ∀ s ∈ M.S, vfa R (fun i : Fin (n * b) => θ i) (iter n) s ≤ Vstar s := by sorry

end SelfGuidedALP
