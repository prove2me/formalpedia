-- Prove2me | Theorems.Thm_PolyContract_lemma_b_5
-- name    : PolyContract.lemma_b_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:52:25.897827+00:00
-- url     : https://prove2.me/theorems/28f3030b-5d71-4e51-9c6c-228cdf020c78
-- title:
--   Lemma B.5 — direct sums, dilation, capped linear summand
-- statement:
--   Let $(f,m,\beta)$ be a valid instance with quadratic costs and best response $x^\star$, and let $\alpha\ge0$.
--
--   1. (a) If $f=f_1\oplus f_2$ for rank functions $f_1,f_2$ on disjoint $E_1,E_2$, then $x^\star=(x^\star_1,x^\star_2)$ and $r(x^\star(\alpha))=r_1(x^\star_1(\alpha))+r_2(x^\star_2(\alpha))$, where $x^\star_i$ and $r_i$ belong to $(f_i,m|_{E_i},\beta|_{E_i})$.
--   2. (b) For $\sigma>0$, the instance $(f,m/\sigma,\beta)$ has the best response $\alpha\mapsto x^\star(\alpha/\sigma)$ and the reward $r(x^\star(\alpha/\sigma))/\sigma$.
--   3. (c) For $C,\alpha_\circ>0$, adding a capped linear summand (an element $e$ with $f(\{e\})=C$, $m_e=1$, $\beta_e=\alpha_\circ/C$) adds $C\min(\alpha/\alpha_\circ,1)$ to the reward under the best response.
--
--   These rules let rewards of combs be added, rescaled along the share axis, and shifted by a constant on a window.
--
--   Differences from the source:
--   - encoding: x⋆ = (x⋆1, x⋆2); the instance has the best response α ↦ x⋆(α/σ) → x is a best response of the sum iff its restrictions are best responses of the summands; x is a best response of the dilated instance at α iff it is one of the original at α/σ; reason: the best response is unique (§3, p.7), so the predicate form says the same
-- source:
--   Klimm, Lippke, Warode, The Complexity of Continuous Contract Design over Polymatroids, arXiv:2611.04934 (version of November 3, 2026, sha256 18cfc0a5…), Lemma B.5, p.22 (PDF p.23)

import Mathlib
import Definitions.Def_PolyContract_InstanceOps

set_option autoImplicit false

namespace PolyContract

/-- **Lemma B.5** (Klimm, Lippke, Warode, arXiv:2611.04934, version of November 3, 2026, sha256
18cfc0a5…, p.22). Let `(f, m, β)` be an instance with best response `x⋆`.

(a) If `f = f₁ ⊕ f₂` for rank functions `f₁, f₂`, then `x⋆ = (x⋆₁, x⋆₂)` and
`r(x⋆(α)) = r₁(x⋆₁(α)) + r₂(x⋆₂(α))`.
(b) For `σ > 0`, the instance `(f, m/σ, β)` has the best response `α ↦ x⋆(α/σ)` and the reward
`r(x⋆(α/σ))/σ` under it.
(c) Let `C, α◦ > 0`. Adding a capped linear summand (an element `e` with `f({e}) := C`, `m_e := 1`,
`β_e := α◦/C`) adds `C min(α/α◦, 1)` to the reward under the best response.

**Formalization Note** Shares are `α ≥ 0`. The instances are valid (rank function, `m ≥ 0`,
`β > 0`, quadratic costs). In (a) the ground set is `ι₁ ⊕ ι₂` and `x⋆ᵢ` is the restriction of
`x⋆` to `ιᵢ`. "The reward under the best response" is `brReward`. -/
theorem lemma_b_5 {ι ι₂ : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype ι₂] [DecidableEq ι₂] [Nonempty ι₂] :
    -- (a)
    (∀ (I₁ : QuadInstance ι) (I₂ : QuadInstance ι₂), I₁.Valid → I₂.Valid →
      ∀ α : ℝ, 0 ≤ α →
        (∀ x : ι ⊕ ι₂ → ℝ, (I₁.directSum I₂).IsBestResponse α x ↔
          I₁.IsBestResponse α (x ∘ Sum.inl) ∧ I₂.IsBestResponse α (x ∘ Sum.inr)) ∧
        (I₁.directSum I₂).brReward α = I₁.brReward α + I₂.brReward α) ∧
    -- (b)
    (∀ I : QuadInstance ι, I.Valid → ∀ σ : ℝ, 0 < σ → ∀ α : ℝ, 0 ≤ α →
      (∀ x : ι → ℝ, (I.dilate σ).IsBestResponse α x ↔ I.IsBestResponse (α / σ) x) ∧
      (I.dilate σ).brReward α = I.brReward (α / σ) / σ) ∧
    -- (c)
    (∀ I : QuadInstance ι, I.Valid → ∀ C α₀ : ℝ, 0 < C → 0 < α₀ → ∀ α : ℝ, 0 ≤ α →
      (I.addCappedLinear C α₀).brReward α = I.brReward α + C * min (α / α₀) 1) := by sorry

end PolyContract
