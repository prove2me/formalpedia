-- Prove2me | Theorems.Thm_SuperstarExcl_Complementors_lemma_1
-- name    : SuperstarExcl.Complementors.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T02:29:55.434971+00:00
-- url     : https://prove2.me/theorems/f3683376-8a7d-4853-90d9-973e5aef536a
-- title:
--   Lemma 1 — equilibrium prices p₁⋆ = F(m⋆)·{1/f(m⋆) − γθ[λ(γD₁⋆) + λ(γD₂⋆)]}, p₂⋆ = (1 − F(m⋆))·{…}
-- statement:
--   Let $g_1,g_2\in\{0,1\}$ and $\phi\in\mathbb R$, and let $(p_1,p_2,D)$ be a price equilibrium in which both platforms are active, $0<D<1$. Write $m^\star$ for the equilibrium indifferent consumer, so that $D=F(m^\star)$ is platform $1$'s consumer share and $1-D$ is platform $2$'s. Then
--   $$
--   p_1=F(m^\star)\Bigl\{\frac{1}{f(m^\star)}-\gamma\theta\bigl[\lambda(\gamma D)+\lambda(\gamma(1-D))\bigr]\Bigr\},
--   $$
--   $$
--   p_2=\bigl(1-F(m^\star)\bigr)\Bigl\{\frac{1}{f(m^\star)}-\gamma\theta\bigl[\lambda(\gamma D)+\lambda(\gamma(1-D))\bigr]\Bigr\}.
--   $$
--
--   The two prices share the same bracket, which mixes consumer differentiation ($1/f$) with the cross-group externality. Their ratio is the ratio of market shares. Every later result uses this characterisation of interior equilibria.
--
--   **Formalization Note** The equilibrium is a best-response (Nash) equilibrium of the pricing game with fulfilled-expectations demand. It is not defined by these formulas: the formulas are the content of the lemma. Interiority makes $m^\star$ lie in $(-\bar m,\bar m)$, where $f(m^\star)>0$, so the division is well defined. The uniqueness discussion in the paper's proof is not part of the statement.
-- source:
--   Carroni, Madio & Shekhar, Superstar Exclusivity in Two-Sided Markets, accepted manuscript (hdl:11585/922035), p. 12, Lemma 1 (proof App. A.1, pp. 34–36)

import Mathlib
import Definitions.Def_SuperstarExcl_Complementors_Model
import Definitions.Def_SuperstarExcl_Complementors_Market

namespace SuperstarExcl.Complementors

theorem lemma_1 (M : Model) (ϕ g₁ g₂ p₁ p₂ D : ℝ)
    (hg₁ : g₁ = 0 ∨ g₁ = 1) (hg₂ : g₂ = 0 ∨ g₂ = 1)
    (heq : IsEquilibrium M ϕ g₁ g₂ p₁ p₂ D) (hD₀ : 0 < D) (hD₁ : D < 1) :
    p₁ = M.F (mstar M ϕ g₁ g₂ p₁ p₂ D) *
        (1 / M.f (mstar M ϕ g₁ g₂ p₁ p₂ D) -
          M.γ * M.θ * (M.lam (M.γ * D) + M.lam (M.γ * (1 - D)))) ∧
      p₂ = (1 - M.F (mstar M ϕ g₁ g₂ p₁ p₂ D)) *
        (1 / M.f (mstar M ϕ g₁ g₂ p₁ p₂ D) -
          M.γ * M.θ * (M.lam (M.γ * D) + M.lam (M.γ * (1 - D)))) := by sorry

end SuperstarExcl.Complementors
