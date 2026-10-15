-- Prove2me | Theorems.Thm_SuperstarExcl_Complementors_lemma_2
-- name    : SuperstarExcl.Complementors.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:30:02.305766+00:00
-- url     : https://prove2.me/theorems/d130620d-89cf-4b91-99bb-33f753cf7030
-- title:
--   Lemma 2 — under non-exclusivity the symmetric equilibrium splits the market, p⋆ = 1/(2f(0)) − γθλ(γ/2)
-- statement:
--   Suppose the Superstar is on both platforms, $g_1=g_2=1$, with any value $\phi$. Let $(p,p,D)$ be a price equilibrium at equal prices with $0<D<1$. Then:
--
--   1. the common price is
--   $$
--   p=\frac{1}{2f(0)}-\gamma\theta\,\lambda(\gamma/2);
--   $$
--   2. the market is split equally: $m^\star=0$ and $D=\tfrac12$;
--   3. the complementor masses are $\Lambda(\gamma D)=\Lambda(\gamma(1-D))=\Lambda(\gamma/2)$;
--   4. every active complementor (one joining at least one platform) multihomes;
--   5. every complementor with $k>\gamma/2$ zerohomes.
--
--   This is the benchmark against which exclusivity is measured. The equal-split share $D=\tfrac12$ is a conclusion, not an assumption. At equal prices, $\tfrac12$ must be shown to be the only interior fulfilled-expectations share.
--
--   **Formalization Note** The paper selects the symmetric outcome under non-exclusivity ("consumers believe that the market will be equally split ... at equal prices", p. 11). The statement encodes this selection as the hypothesis that the two prices are equal.
-- source:
--   Carroni, Madio & Shekhar, Superstar Exclusivity in Two-Sided Markets, accepted manuscript (hdl:11585/922035), p. 12, Lemma 2 (proof App. A.2, pp. 36–37)

import Mathlib
import Definitions.Def_SuperstarExcl_Complementors_Model
import Definitions.Def_SuperstarExcl_Complementors_Market

namespace SuperstarExcl.Complementors

theorem lemma_2 (M : Model) (ϕ p D : ℝ)
    (heq : IsEquilibrium M ϕ 1 1 p p D) (hD₀ : 0 < D) (hD₁ : D < 1) :
    p = 1 / (2 * M.f 0) - M.γ * M.θ * M.lam (M.γ / 2) ∧
      mstar M ϕ 1 1 p p D = 0 ∧ D = 1 / 2 ∧
      M.Λ (M.γ * D) = M.Λ (M.γ / 2) ∧ M.Λ (M.γ * (1 - D)) = M.Λ (M.γ / 2) ∧
      (∀ k, (Joins M D k ∨ Joins M (1 - D) k) → Multihomes M D (1 - D) k) ∧
      (∀ k, M.γ / 2 < k → Zerohomes M D (1 - D) k) := by sorry

end SuperstarExcl.Complementors
