-- Prove2me | Theorems.Thm_SaddleSplit_Async_proposition_2_5
-- name    : SaddleSplit.Async.proposition_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:17:29.115992+00:00
-- url     : https://prove2.me/theorems/50f1e211-ecfc-4ae7-b772-c0e33c5d117e
-- title:
--   Proposition 2.5, p. 9 — 𝓢 = 𝐌 + 𝐂 with 𝐌 maximally monotone and 𝐂 α-cocoercive; half-spaces containing zer 𝓢
-- statement:
--   In the setting of Problem 1.1 and of Definitions 2.1 and 2.4, with $\mathbf M$ the operator (2.28) and $\mathbf C$ the operator (2.29) on $\mathbf X$:
--
--   1. $\boldsymbol{\mathcal S}=\mathbf M+\mathbf C$;
--   2. $\mathbf M$ is maximally monotone;
--   3. with $\alpha=\min\{\alpha^c_i,\beta^c_k,\delta^c_k\}_{i\in I,k\in K}$: (a) $\mathbf C$ is $\alpha$-cocoercive; (b) for every $(\mathbf p,\mathbf p^*)\in\operatorname{gra}\mathbf M$ and every $\mathbf q\in\mathbf X$,
--   $$\operatorname{zer}\boldsymbol{\mathcal S}\subset\big\{\mathbf x\in\mathbf X\ \big|\ \langle\mathbf x-\mathbf p\mid\mathbf p^*+\mathbf C\mathbf q\rangle\le(4\alpha)^{-1}\|\mathbf p-\mathbf q\|^2\big\}.$$
--
--   Part 3(b) is the source of the half-spaces onto which the outer-approximation iteration (2.32) and Algorithm 3.4 project.
--
--   **Formalization Note** $\mathbf M+\mathbf C$ is the sum of a set-valued and a single-valued operator, $(\mathbf M+\mathbf C)\mathbf x=\{\mathbf u+\mathbf C\mathbf x\mid \mathbf u\in\mathbf M\mathbf x\}$. α enters as any real that is the least element of the set of all cocoercivity constants.
-- source:
--   Bùi & Combettes, Multivariate monotone inclusions in saddle form, arXiv:2002.06135v3, p. 9, Proposition 2.5 (proof pp. 9–10)

import Mathlib
import Definitions.Def_SaddleSplit_Async_Setting

namespace SaddleSplit.Async
open InnerProductSpace Filter Topology
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR

/-- Proposition 2.5, p. 9: (i) `𝓢 = 𝐌 + 𝐂`; (ii) `𝐌` is maximally monotone; (iii) with
`α = min{αᶜ_i, βᶜ_k, δᶜ_k}`: (a) `𝐂` is `α`-cocoercive, and (b) for `(𝐩, 𝐩*) ∈ gra 𝐌` and
`𝐪 ∈ 𝐗`, `zer 𝓢 ⊂ {𝐱 | ⟪𝐱 − 𝐩, 𝐩* + 𝐂𝐪⟫ ≤ (4α)⁻¹‖𝐩 − 𝐪‖²}`. -/
theorem proposition_2_5 {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
    {H : I → Type*} [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)]
    [∀ i, CompleteSpace (H i)]
    {G : K → Type*} [∀ k, NormedAddCommGroup (G k)] [∀ k, InnerProductSpace ℝ (G k)]
    [∀ k, CompleteSpace (G k)]
    (prob : Problem H G) (hprob : prob.Hyp) :
    saddleOp prob = addSV (opM prob) (opC prob) ∧
    IsMaximalMonotone (opM prob) ∧
    ∀ α : ℝ, IsLeast (Set.range prob.αc ∪ Set.range prob.βc ∪ Set.range prob.δc) α →
      IsCocoercive α (opC prob) ∧
      ∀ p ps q : XSpace H G, ps ∈ opM prob p →
        zer (saddleOp prob) ⊆
          {X | ⟪X - p, ps + opC prob q⟫_ℝ ≤ (4 * α)⁻¹ * ‖p - q‖ ^ 2} := by sorry

end SaddleSplit.Async
