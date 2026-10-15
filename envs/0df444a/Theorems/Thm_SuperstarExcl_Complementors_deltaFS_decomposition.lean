-- Prove2me | Theorems.Thm_SuperstarExcl_Complementors_deltaFS_decomposition
-- name    : SuperstarExcl.Complementors.deltaFS_decomposition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:30:05.862785+00:00
-- url     : https://prove2.me/theorems/db0bde2f-c4db-43b4-b8ab-b8a488df7a96
-- title:
--   Section 4.3, p. 17 — decomposition of ΔFS = FS⋆(1,0) − FS⋆(1,1) into multihomers, switchers and entrants
-- statement:
--   Let $D_1,D_2$ be consumer shares with $D_1+D_2=1$ and $\tfrac12\le D_1\le1$. Let $FS(D_1,D_2)$ be the complementors' total surplus at these shares. Let
--   $$FS^\star(1,1)=\int_0^{\gamma/2}(\gamma-2k)\lambda(k)\,dk$$
--   be the surplus at the equal split. Then
--   $$
--   FS(D_1,D_2)-FS^\star(1,1)=0\cdot\int_0^{\gamma D_2}\lambda(k)\,dk+\int_{\gamma D_2}^{\gamma/2}\bigl(\gamma(D_1-1)+k\bigr)\lambda(k)\,dk+\int_{\gamma/2}^{\gamma D_1}(\gamma D_1-k)\lambda(k)\,dk .
--   $$
--
--   The three terms are the change in surplus of complementors who multihome in both regimes (zero), of those who switch from multihoming to singlehoming on platform $1$, and of entrants who were inactive under non-exclusivity. With $D_1=D^\star_1(1,0)$ and $D_2=D^\star_2(0,1)$ this is the paper's decomposition of the net gain $\Delta FS$ from exclusivity.
--
--   **Formalization Note** The identity is stated for every pair of shares in the given range, not only for equilibrium shares, since it uses nothing about equilibrium. The integrals are oriented interval integrals with the paper's limits.
-- source:
--   Carroni, Madio & Shekhar, Superstar Exclusivity in Two-Sided Markets, accepted manuscript (hdl:11585/922035), p. 17, Section 4.3, decomposition of ΔFS (derivation App. A.4, pp. 40–41)

import Mathlib
import Definitions.Def_SuperstarExcl_Complementors_Model
import Definitions.Def_SuperstarExcl_Complementors_Market

namespace SuperstarExcl.Complementors

theorem deltaFS_decomposition (M : Model) (D₁ D₂ : ℝ) (hsum : D₁ + D₂ = 1)
    (hD₁ : 1 / 2 ≤ D₁) (hD₁' : D₁ ≤ 1) :
    FS M D₁ D₂ - ∫ k in (0)..(M.γ / 2), (M.γ - 2 * k) * M.lam k =
      0 * (∫ k in (0)..(M.γ * D₂), M.lam k) +
        (∫ k in (M.γ * D₂)..(M.γ / 2), (M.γ * (D₁ - 1) + k) * M.lam k) +
        ∫ k in (M.γ / 2)..(M.γ * D₁), (M.γ * D₁ - k) * M.lam k := by sorry

end SuperstarExcl.Complementors
