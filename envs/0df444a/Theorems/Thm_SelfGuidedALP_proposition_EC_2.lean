-- Prove2me | Theorems.Thm_SelfGuidedALP_proposition_EC_2
-- name    : SelfGuidedALP.proposition_EC_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:29:32.670487+00:00
-- url     : https://prove2.me/theorems/30b30815-7332-4e19-accb-3a59e628a428
-- title:
--   Proposition EC.2, p.ec8 — $\mathcal B$ is Hilbert, $\bar{\mathcal B}_N$ is closed, and $B^*$ splits orthogonally
-- statement:
--   Let $(\beta_0^*,B^*)$ be a representation of $V^*$ and $\theta^1,\dots,\theta^N$ samples. Then:
--
--   1. $\mathcal B$ with the inner product $\langle B,B'\rangle_{\mathcal B}=\int_\Theta B B'/\rho\,\mathrm d\theta$ is a Hilbert space;
--   2. $\bar{\mathcal B}_N$ is a closed subset of $\mathcal B$ under addition and scalar multiplication;
--   3. there are $B^{*,o}_N\in\bar{\mathcal B}_N$ and $B^{*,\perp}_N\in\bar{\mathcal B}_N^\perp$ with $B^*=B^{*,o}_N+B^{*,\perp}_N$ and
--   $$
--   \|B^*/\rho\|_{2,\rho}^2=\|B^{*,o}_N/\rho\|_{2,\rho}^2+\|B^{*,\perp}_N/\rho\|_{2,\rho}^2 .
--   $$
--
--   The decomposition isolates the part of $B^*$ left to approximate after the first $N$ samples.
--
--   **Formalization Note** Under the printed Definition EC.2 the closure $\bar{\mathcal B}_N$ is $\{0\}$, so the decomposition is $B^*=0+B^*$.
--
--   Differences from the source:
--   - encoding: ‖B*/ρ‖_{2,ρ} = ‖B^{*,o}_N/ρ‖_{2,ρ} + ‖B^{*,⊥}_N/ρ‖_{2,ρ}, with the printed integrals → the same identity with each printed integral written as the square of the norm of ℬ; reason: the printed ‖·‖_{2,ρ} is the square of the norm of ℬ, so this is the printed identity
--   - reading: (β*₀,B*) an optimal solution to FELP (associated to V*) → every representation (β*₀,B*) of V* with B* ∈ ℬ; reason: the proofs use only V* = V(·;(β*₀,B*)); a FELP optimum that does not represent V* (say ν a point mass) would break (EC.12), and every representation is FELP-optimal by the proof of Proposition 1
--   - reading: N iid samples from ρ, no probability in the conclusion → every θ¹,…,θᴺ ∈ Θ; reason: the claim is deterministic in the samples, and iid samples lie in Θ almost surely
--   - reading: Assumption 2 not repeated in the statement → Assumption 2 is a hypothesis; reason: p.ec1: Assumptions 1 and 2 hold for all proofs in the electronic companion
--   - encoding: V* := PC(·,π*) for an optimal stationary policy (Assumption 1, p.7) → V is continuous on S and solves the Bellman optimality equation with the minimum attained; reason: the paper uses V* only through this equation (p.8, p.ec2); with γ < 1 its continuous solution is unique, and it is the optimal value under Assumption EC.1
--   - generalization: Assumption EC.1 and the existence of π* (pp.7, ec1) → dropped: no boundedness, semicontinuity or kernel continuity is assumed; reason: those conditions only guarantee that V* exists and solves the Bellman equation, which is now a hypothesis; a paper instance satisfies the Lean hypotheses
--   - encoding: each action set is continuous compact or finite → each A s is a nonempty compact subset of ℝᵐ; reason: a finite set is compact, so both cases are covered
--   - reading: integrals dθ with a sampling density ρ(θ) on Θ ⊆ ℝ^{d+1} → dθ is Lebesgue measure on ℝ^{d+1} and ρ a density for it; reason: the paper never names another reference measure, and its Definition EC.2 calls ℬ an L² space; laws without a Lebesgue density (Table 1's sphere and stump, p.8) are outside this reading
-- source:
--   Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, Proposition EC.2, p.ec8

import Mathlib
import Definitions.Def_SelfGuidedALP_Assumption2
import Definitions.Def_SelfGuidedALP_IsOptimalValue
import Definitions.Def_SelfGuidedALP_BNbar

open MeasureTheory

namespace SelfGuidedALP

/-- Proposition EC.2 of Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, p.ec8: (i) `ℬ` with `⟨·,·⟩_ℬ` is a Hilbert space; (ii) `ℬ̄_N` is a
closed subspace of `ℬ`; (iii) `B* = B^{*,o}_N + B^{*,⊥}_N` with `B^{*,o}_N ∈ ℬ̄_N`,
`B^{*,⊥}_N ∈ ℬ̄_N^⊥`, and the printed identity between the quantities `∫ B²/ρ dθ`, which are the
squares of the norm. -/
theorem proposition_EC_2 {d m N : ℕ} (M : MDP d m) (R : RBClass d) (L : ℝ)
    (Vstar : EuclideanSpace ℝ (Fin d) → ℝ) (hVstar : IsOptimalValue M Vstar)
    (hA2 : Assumption2 M R L Vstar) (βs : ℝ) (Bs : Bspace R) (hrep : IsRep M R Vstar βs Bs)
    (θs : Fin N → EuclideanSpace ℝ (Fin (d + 1))) (hθs : ∀ i, θs i ∈ R.Θ) :
    (CompleteSpace (Bspace R) ∧
        ∀ B B' : Bspace R, inner ℝ B B' = ∫ θ in R.Θ, B θ * B' θ / R.ρ θ) ∧
      IsClosed (BNbar R θs : Set (Bspace R)) ∧
      ∃ Bo ∈ BNbar R θs, ∃ Bp ∈ (BNbar R θs)ᗮ,
        Bs = Bo + Bp ∧ ‖Bs‖ ^ 2 = ‖Bo‖ ^ 2 + ‖Bp‖ ^ 2 := by sorry

end SelfGuidedALP
