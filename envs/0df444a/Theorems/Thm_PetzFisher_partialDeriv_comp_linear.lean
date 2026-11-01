-- Prove2me | Theorems.Thm_PetzFisher_partialDeriv_comp_linear
-- name    : PetzFisher.partialDeriv_comp_linear
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:28:18.616985+00:00
-- url     : https://prove2.me/theorems/6546e8b5-1787-4f65-9cfa-9efa283c1ed9
-- title:
--   Proof of Theorem 2.3 — $\mathbb J^{-1}_{\beta(\rho(\theta))}\beta(B_i(\theta))$ is the score operator of $\beta(\mathcal M)$
-- statement:
--   Let $\beta:M_n\to M_m$ be a linear map, $G\subseteq\mathbb R^k$ open, and $\theta\mapsto\rho(\theta)\in M_n$ differentiable on $G$; set $B_i(\theta):=\partial_{\theta_i}\rho(\theta)$. Then:
--
--   1. the image family $\theta\mapsto\beta(\rho(\theta))$ is differentiable on $G$;
--   2. for every $\theta\in G$ and $i$, $\partial_{\theta_i}\beta(\rho(\theta))=\beta(B_i(\theta))$;
--   3. consequently, for every $f$, the score operator (25) of $\beta(\mathcal M)=\{\beta(\rho(\theta))\}$ is
--   $$
--   L^f_i(\theta)=\big(\mathbb J^f_{\beta(\rho(\theta))}\big)^{-1}\beta\big(B_i(\theta)\big).
--   $$
--
--   This is the first step of the proof of Theorem 2.3: it expresses the Fisher information matrix of the coarse-grained family through the tangent vectors $B_i(\theta)$ of the original one.
--
--   **Formalization Note** Differentiability and partial derivatives are entrywise. Only linearity of $\beta$ is used.
--
--   Differences from the source:
--   - generalization: β completely positive and trace preserving → β any ℂ-linear map; reason: the step uses only linearity; CPTP maps are linear
--   - generalization: smooth k-dimensional manifold → entrywise differentiable on an open G ⊆ ℝᵏ, no injectivity or immersion condition; reason: only the partial derivatives are used; a smooth parametrization is an instance
--   - encoding: "is the score operator of β(𝓜)" → the score operator (25) of the family θ ↦ β(ρ(θ)) equals 𝕁^{-1}_{β(ρ(θ))}β(B_i(θ)), together with the differentiability and chain-rule clauses it rests on; reason: (25) applied to the image family
-- source:
--   Petz–Ghinea, Introduction to quantum Fisher information, arXiv:1008.2417v1, proof of Theorem 2.3, first sentence, p.15

import Mathlib
import Definitions.Def_PetzFisher_partialDeriv
import Definitions.Def_PetzFisher_scoreOperator

open scoped Matrix ComplexOrder

namespace PetzFisher

/-- Petz–Ghinea, *Introduction to quantum Fisher information*, arXiv:1008.2417v1, proof of
Theorem 2.3, first sentence, p.15: "We set `B_i(θ) := ∂_{θ_i} ρ(θ)`. Then
`𝕁^{-1}_{β(ρ(θ))} β(B_i(θ))` is the score operator of `β(𝓜)`."

For a linear map `β : Mₙ → Mₘ` and a family `θ ↦ ρ(θ)` entrywise differentiable on an open set
`G ⊆ ℝᵏ`: the image family `θ ↦ β(ρ(θ))` is entrywise differentiable on `G`, and at every `θ ∈ G`
its partial derivatives are `∂_{θ_i} β(ρ(θ)) = β(B_i(θ))`, so that its score operator (25) is
`L^f_i(θ) = (𝕁^f_{β(ρ(θ))})^{-1}(β(B_i(θ)))`.

**Formalization Note.** Only ℂ-linearity of `β` is used; complete positivity and trace
preservation, which the theorem assumes, are not needed for this step. The score-operator clause
holds for every `f : ℝ → ℝ`. -/
theorem partialDeriv_comp_linear {I J : Type} [Fintype I] [DecidableEq I] [Fintype J]
    [DecidableEq J] {k : ℕ} (β : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ)
    (G : Set (Fin k → ℝ)) (hG : IsOpen G) (ρ : (Fin k → ℝ) → Matrix I I ℂ)
    (hdiff : ∀ a b, DifferentiableOn ℝ (fun θ => ρ θ a b) G) :
    (∀ a b, DifferentiableOn ℝ (fun θ => β (ρ θ) a b) G) ∧
    (∀ θ ∈ G, ∀ i : Fin k, partialDeriv (fun θ' => β (ρ θ')) θ i = β (partialDeriv ρ θ i)) ∧
    (∀ (f : ℝ → ℝ), ∀ θ ∈ G, ∀ i : Fin k,
      scoreOperator f (fun θ' => β (ρ θ')) θ i =
        QAlgorithms.Papers.Independent.Bridge50.P31.inverseMetric f (β (ρ θ))
          (β (partialDeriv ρ θ i))) := by sorry

end PetzFisher
