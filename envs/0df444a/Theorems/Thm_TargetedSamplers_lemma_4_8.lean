-- Prove2me | Theorems.Thm_TargetedSamplers_lemma_4_8
-- name    : TargetedSamplers.lemma_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:09:35.04534+00:00
-- url     : https://prove2.me/theorems/98b86f9a-1e8c-4507-8bfc-8539759c521b
-- title:
--   Lemma 4.8 — composing somewhere-condensers
-- statement:
--   Let $C_1:\{0,1\}^{n_1}\to(\{0,1\}^{n_2})^{\ell_1}$ be a $[\rho_1\mapsto\rho_2]^{1:\ell_1}_{\sim\gamma_1}$-somewhere-condenser and $C_2:\{0,1\}^{n_2}\to(\{0,1\}^{n_3})^{\ell_2}$ a $[\rho_2\mapsto\rho_3]^{1:\ell_2}_{\sim\gamma_2}$-somewhere-condenser. Let $C:\{0,1\}^{n_1}\to(\{0,1\}^{n_3})^{\ell_1\ell_2}$ apply $C_2$ to each of the $\ell_1$ outputs of $C_1$. Then
--   $$C\ \text{is a}\ [\rho_1\mapsto\rho_3]^{1:\ell_1\ell_2}_{\sim\gamma_1+\gamma_2}\text{-somewhere-condenser.}$$
--
--   The lemma is what lets the basic somewhere-condenser of Zuckerman be iterated in Theorem 4.13.
--
--   Differences from the source:
--   - encoding: outputs indexed by [ℓ₁], [ℓ₂] and [ℓ₁ℓ₂] → finite index types ι₁, ι₂ and ι₁ × ι₂; reason: a relabelling of the coordinates; the same instances
--   - reading: γ-close: "L1 norm (i.e. statistical distance)" → statistical distance ½‖P−Q‖₁ ≤ γ; reason: the page equates the two; statistical distance is the standard notion for condensers
-- source:
--   Chen, Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027 submission (manuscript sha256 599d0a59…), Lemma 4.8, p.21 (pdf p.23)

import Mathlib
import Definitions.Def_TargetedSamplers_IsSomewhereCondenser

namespace TargetedSamplers

/-- Lemma 4.8 (Composing Somewhere-Condensers, extended from [BKS+10, Lemma 5.5]) (Chen, Doron,
Ebtehaj, Tell, Targeted Samplers, STOC 2027 submission, manuscript sha256 599d0a59…, p.21). If
`C₁ : {0,1}^{n₁} → ({0,1}^{n₂})^{ℓ₁}` is a `[ρ₁ ↦ ρ₂]^{1:ℓ₁}_{∼γ₁}`-somewhere-condenser and
`C₂ : {0,1}^{n₂} → ({0,1}^{n₃})^{ℓ₂}` a `[ρ₂ ↦ ρ₃]^{1:ℓ₂}_{∼γ₂}`-somewhere-condenser, then the map
applying `C₂` to each of the `ℓ₁` outputs of `C₁` is a `[ρ₁ ↦ ρ₃]^{1:ℓ₁ℓ₂}_{∼γ₁+γ₂}`-somewhere-condenser.

**Formalization Note** The `ℓ₁ℓ₂` outputs of the composition are indexed by `ι₁ × ι₂`. -/
theorem lemma_4_8 {ι₁ ι₂ : Type} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    {n₁ n₂ n₃ : ℕ} (ρ₁ ρ₂ ρ₃ γ₁ γ₂ : ℝ)
    (C₁ : (Fin n₁ → Bool) → ι₁ → Fin n₂ → Bool) (C₂ : (Fin n₂ → Bool) → ι₂ → Fin n₃ → Bool)
    (h₁ : IsSomewhereCondenser ρ₁ ρ₂ γ₁ C₁) (h₂ : IsSomewhereCondenser ρ₂ ρ₃ γ₂ C₂) :
    IsSomewhereCondenser ρ₁ ρ₃ (γ₁ + γ₂) (fun x (p : ι₁ × ι₂) => C₂ (C₁ x p.1) p.2) := by sorry

end TargetedSamplers
