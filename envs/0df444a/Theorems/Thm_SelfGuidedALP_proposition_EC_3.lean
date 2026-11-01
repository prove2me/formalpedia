-- Prove2me | Theorems.Thm_SelfGuidedALP_proposition_EC_3
-- name    : SelfGuidedALP.proposition_EC_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:29:36.144041+00:00
-- url     : https://prove2.me/theorems/54faaa39-b7c9-40e1-9136-9571c4263573
-- title:
--   Proposition EC.3, p.ec9 — $B^{*,o}_N$ is replaced by $B^\zeta_N\in\mathcal B_N$ up to $\zeta$
-- statement:
--   Let $\zeta>0$, let $\theta^1,\dots,\theta^N$ be samples, and let $(\beta_0^*,B^*)$ represent $V^*$ with $B^*=B^{*,o}_N+B^{*,\perp}_N$ for some $B^{*,o}_N\in\bar{\mathcal B}_N$ and $B^{*,\perp}_N\in\bar{\mathcal B}_N^\perp$. Put $\boldsymbol\beta^{*,\perp}_N:=(0,B^{*,\perp}_N)$. There is $B^\zeta_N\in\mathcal B_N$ such that $\boldsymbol\beta^\zeta_N:=(\beta_0^*,B^\zeta_N)$ satisfies
--   $$
--   \bigl\|V^*-\bigl(V(\boldsymbol\beta^\zeta_N)+V(\boldsymbol\beta^{*,\perp}_N)\bigr)\bigr\|_\infty\le\zeta .
--   $$
--   Moreover $V(\cdot;\boldsymbol\beta^\zeta_N)=\beta_0^*+\sum_{i=1}^N\beta^\zeta_i\varphi(\cdot;\theta^i)$ for some coefficients $\beta^\zeta_i\in\mathbb R$.
--
--   This reduces the approximation of $V^*$ to that of $V(\boldsymbol\beta^{*,\perp}_N)$ by the new bases.
--
--   Differences from the source:
--   - reading: (β*₀,B*) an optimal solution to FELP (associated to V*) → every representation (β*₀,B*) of V* with B* ∈ ℬ; reason: the proofs use only V* = V(·;(β*₀,B*)); a FELP optimum that does not represent V* (say ν a point mass) would break (EC.12), and every representation is FELP-optimal by the proof of Proposition 1
--   - reading: N iid samples from ρ, no probability in the conclusion → every θ¹,…,θᴺ ∈ Θ; reason: the claim is deterministic in the samples, and iid samples lie in Θ almost surely
--   - reading: Assumption 2 not repeated in the statement → Assumption 2 is a hypothesis; reason: p.ec1: Assumptions 1 and 2 hold for all proofs in the electronic companion
--   - encoding: V* := PC(·,π*) for an optimal stationary policy (Assumption 1, p.7) → V is continuous on S and solves the Bellman optimality equation with the minimum attained; reason: the paper uses V* only through this equation (p.8, p.ec2); with γ < 1 its continuous solution is unique, and it is the optimal value under Assumption EC.1
--   - generalization: Assumption EC.1 and the existence of π* (pp.7, ec1) → dropped: no boundedness, semicontinuity or kernel continuity is assumed; reason: those conditions only guarantee that V* exists and solves the Bellman equation, which is now a hypothesis; a paper instance satisfies the Lean hypotheses
--   - encoding: each action set is continuous compact or finite → each A s is a nonempty compact subset of ℝᵐ; reason: a finite set is compact, so both cases are covered
--   - reading: integrals dθ with a sampling density ρ(θ) on Θ ⊆ ℝ^{d+1} → dθ is Lebesgue measure on ℝ^{d+1} and ρ a density for it; reason: the paper never names another reference measure, and its Definition EC.2 calls ℬ an L² space; laws without a Lebesgue density (Table 1's sphere and stump, p.8) are outside this reading
-- source:
--   Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, Proposition EC.3, eq. (EC.12), p.ec9

import Mathlib
import Definitions.Def_SelfGuidedALP_Assumption2
import Definitions.Def_SelfGuidedALP_IsOptimalValue
import Definitions.Def_SelfGuidedALP_BNbar
import Definitions.Def_SelfGuidedALP_vfa

open MeasureTheory

namespace SelfGuidedALP

/-- Proposition EC.3 of Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, eq. (EC.12), p.ec9: for `B* = B^{*,o}_N + B^{*,⊥}_N` and `ζ > 0`
there is `B^ζ_N ∈ ℬ_N` with `‖V* − (V(β^ζ_N) + V(β^{*,⊥}_N))‖_∞ ≤ ζ`, where
`β^ζ_N := (β*₀, B^ζ_N)` and `β^{*,⊥}_N := (0, B^{*,⊥}_N)`; moreover
`V(·;β^ζ_N) = β*₀ + ∑ᵢ β^ζ_i ϕ(·;θⁱ)` for some coefficients. -/
theorem proposition_EC_3 {d m N : ℕ} (M : MDP d m) (R : RBClass d) (L : ℝ)
    (Vstar : EuclideanSpace ℝ (Fin d) → ℝ) (hVstar : IsOptimalValue M Vstar)
    (hA2 : Assumption2 M R L Vstar) (βs : ℝ) (Bs : Bspace R) (hrep : IsRep M R Vstar βs Bs)
    (θs : Fin N → EuclideanSpace ℝ (Fin (d + 1))) (hθs : ∀ i, θs i ∈ R.Θ) (ζ : ℝ) (hζ : 0 < ζ)
    (Bo Bp : Bspace R) (hBo : Bo ∈ BNbar R θs) (hBp : Bp ∈ (BNbar R θs)ᗮ) (hdecomp : Bs = Bo + Bp) :
    ∃ Bz ∈ BN R θs,
      (∀ s ∈ M.S, |Vstar s - (intVFA R βs Bz s + intVFA R 0 Bp s)| ≤ ζ) ∧
        ∃ βz : Fin N → ℝ, ∀ s ∈ M.S,
          intVFA R βs Bz s = βs + ∑ i, βz i * feat R.ϕ (θs i) s := by sorry

end SelfGuidedALP
