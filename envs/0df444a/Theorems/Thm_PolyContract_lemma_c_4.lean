-- Prove2me | Theorems.Thm_PolyContract_lemma_c_4
-- name    : PolyContract.lemma_c_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:54:22.552866+00:00
-- url     : https://prove2.me/theorems/30db234a-f389-4f8c-98d3-510266380ec1
-- title:
--   Lemma C.4 — dilating and adding combs
-- statement:
--   Let all instances be valid with quadratic costs.
--
--   1. (a) Replacing $m$ by $m/\sigma$, $\sigma>0$, in a comb with contact set $\Gamma$, line $p+q\alpha$, dip $\kappa$ and width $\delta$ gives a comb with contact set $\sigma\Gamma$, line $p/\sigma+q\alpha/\sigma^2$, dip $\kappa/\sigma^2$ and width $\sigma\delta$.
--   2. (b) If $I_1$ and $I_2$ are combs on disjoint ground sets with the same width $\delta$, contact sets $\Gamma_1,\Gamma_2\subseteq\delta\mathbb Z$, lines $L_1,L_2$ and dips $\kappa_1,\kappa_2$, then $I_1\oplus I_2$ is a comb with contact set $\Gamma_1\cap\Gamma_2$, line $L_1+L_2$, dip $\min(\kappa_1,\kappa_2)$ and width $\delta/2$.
--
--   Part (b) is how the reduction turns two combs into one whose contacts are exactly the common contacts.
--
--   Differences from the source: none.
-- source:
--   Klimm, Lippke, Warode, The Complexity of Continuous Contract Design over Polymatroids, arXiv:2611.04934 (version of November 3, 2026, sha256 18cfc0a5…), Lemma C.4, p.51 (PDF p.52)

import Mathlib
import Definitions.Def_PolyContract_InstanceOps
import Definitions.Def_PolyContract_IsComb

set_option autoImplicit false

namespace PolyContract

/-- **Lemma C.4** (Klimm, Lippke, Warode, arXiv:2611.04934, version of November 3, 2026, sha256
18cfc0a5…, p.51): dilating and adding combs.

(a) Replacing `m` by `m/σ`, `σ > 0`, in a comb with contact set `Γ`, line `p + qα`, dip `κ` and
width `δ` gives a comb with contact set `σΓ`, line `p/σ + qα/σ²`, dip `κ/σ²` and width `σδ`.
(b) If `I₁` and `I₂` are combs on disjoint ground sets with the same width `δ`, contact sets
`Γ₁, Γ₂ ⊆ δℤ`, lines `L₁, L₂` and dips `κ₁, κ₂`, then `I₁ ⊕ I₂` is a comb with contact set
`Γ₁ ∩ Γ₂`, line `L₁ + L₂`, dip `min(κ₁, κ₂)` and width `δ/2`.

**Formalization Note** The instances are valid instances with quadratic costs. Disjoint ground
sets are the sum type `ι₁ ⊕ ι₂`. `δℤ` is `{δz : z ∈ ℤ}`. -/
theorem lemma_c_4 {ι ι₂ : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype ι₂] [DecidableEq ι₂] [Nonempty ι₂] :
    -- (a)
    (∀ (I : QuadInstance ι) (Γ : Set ℝ) (p q κ δ σ : ℝ), I.Valid → IsComb I Γ p q κ δ → 0 < σ →
      IsComb (I.dilate σ) ((fun γ => σ * γ) '' Γ) (p / σ) (q / σ ^ 2) (κ / σ ^ 2) (σ * δ)) ∧
    -- (b)
    (∀ (I₁ : QuadInstance ι) (I₂ : QuadInstance ι₂) (Γ₁ Γ₂ : Set ℝ) (p₁ q₁ p₂ q₂ κ₁ κ₂ δ : ℝ),
      I₁.Valid → I₂.Valid → IsComb I₁ Γ₁ p₁ q₁ κ₁ δ → IsComb I₂ Γ₂ p₂ q₂ κ₂ δ →
      Γ₁ ⊆ {x | ∃ z : ℤ, x = δ * z} → Γ₂ ⊆ {x | ∃ z : ℤ, x = δ * z} →
      IsComb (I₁.directSum I₂) (Γ₁ ∩ Γ₂) (p₁ + p₂) (q₁ + q₂) (min κ₁ κ₂) (δ / 2)) := by sorry

end PolyContract
