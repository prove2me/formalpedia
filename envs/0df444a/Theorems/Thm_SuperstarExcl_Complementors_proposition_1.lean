-- Prove2me | Theorems.Thm_SuperstarExcl_Complementors_proposition_1
-- name    : SuperstarExcl.Complementors.proposition_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T02:30:00.26026+00:00
-- url     : https://prove2.me/theorems/019da946-4c00-4cd3-8ccc-d1a24b8688a3
-- title:
--   Proposition 1 — exclusivity fosters complementor entry and induces singlehoming
-- statement:
--   Let $\phi>0$, with the Superstar exclusive on platform $1$, and let $(p_1(t),p_2(t),D(t))_{t\in[0,\phi]}$ be the selected exclusivity outcome as in Lemma 3. Write $D^\star_1=D(\phi)$ and $D^\star_2=1-D(\phi)$. Then:
--
--   1. complementors with $k\in(0,\gamma D^\star_2]$ multihome;
--   2. complementors with $k\in(\gamma D^\star_2,\gamma D^\star_1]$ singlehome on platform $1$;
--   3. complementors with $k\in(\gamma D^\star_1,\infty)$ zerohome;
--   4. exclusivity fosters entry: $\Lambda(\gamma D^\star_1)>\Lambda(\gamma/2)$, so more complementors are active than the $\Lambda(\gamma/2)$ active under non-exclusivity (Lemma 2);
--   5. exclusivity induces singlehoming: $\gamma D^\star_2<\gamma D^\star_1$, so the interval of item 2 is nonempty.
--
--   The proposition describes how complementors sort across the two platforms under exclusivity. The surplus comparison of Proposition 3 integrates over this partition.
--
--   **Formalization Note** A type-$k$ complementor joins platform $i$ if and only if $k\le\gamma D_i$. Platform $2$'s share is written $1-D(\phi)$.
-- source:
--   Carroni, Madio & Shekhar, Superstar Exclusivity in Two-Sided Markets, accepted manuscript (hdl:11585/922035), p. 13, Proposition 1

import Mathlib
import Definitions.Def_SuperstarExcl_Complementors_Model
import Definitions.Def_SuperstarExcl_Complementors_Market

namespace SuperstarExcl.Complementors

theorem proposition_1 (M : Model) (ϕ : ℝ) (hϕ : 0 < ϕ) (p₁ p₂ D : ℝ → ℝ)
    (hpath : IsExclusivePath M ϕ p₁ p₂ D) :
    (∀ k, 0 < k → k ≤ M.γ * (1 - D ϕ) → Multihomes M (D ϕ) (1 - D ϕ) k) ∧
      (∀ k, M.γ * (1 - D ϕ) < k → k ≤ M.γ * D ϕ → SinglehomesOn1 M (D ϕ) (1 - D ϕ) k) ∧
      (∀ k, M.γ * D ϕ < k → Zerohomes M (D ϕ) (1 - D ϕ) k) ∧
      M.Λ (M.γ / 2) < M.Λ (M.γ * D ϕ) ∧
      M.γ * (1 - D ϕ) < M.γ * D ϕ := by sorry

end SuperstarExcl.Complementors
