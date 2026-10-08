-- Prove2me | Theorems.Thm_RobertsonSeymour2010_GM23_Immersion_no_descending_shadows
-- name    : RobertsonSeymour2010.GM23.Immersion.no_descending_shadows
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:12:34.735982+00:00
-- url     : https://prove2.me/theorems/710bd207-1a38-4d71-befa-945231ae8c3e
-- title:
--   3.2 — there is no infinite strictly descending sequence of shadows
-- statement:
--   Fix two disjoint countably infinite sets $\Gamma_1,\Gamma_2$ of "new" elements, and order shadows
--   $$\Sigma=(\Omega_\infty, m, \Omega_m,\dots,\Omega_1, R_2, R_1)$$
--   lexicographically as in the definition (first by $\Omega_\infty$ under the proper-ideal order, then by $m$, then by $\Omega_m,\dots,\Omega_1$ from the top index down, then by strict inclusion of $R_2$, then by inclusion of $R_1$). Then there is no sequence of shadows $\Sigma_1,\Sigma_2,\dots$ with
--   $$\Sigma_{i+1}<\Sigma_i\qquad\text{for all } i\ge1 .$$
--
--   This is the well-foundedness that lets the paper choose a minimal ("sharp") evil shadow; the paper states that it follows from 3.1.
--
--   **Formalization Note.** `Γ₁ Γ₂ : Set X` are disjoint and infinite (the paper's "countably infinite" is weakened to "infinite"; the statement does not depend on it). The sequence is indexed from $0$. `Shadow.Lt` is `Shadow.Le` together with the negation of `Shadow.Same`, which compares quasi-orders by ground set and order and compares only $\Omega_1,\dots,\Omega_m$.
-- source:
--   Robertson, Seymour, Graph Minors XXIII. Nash-Williams' immersion conjecture (authors' manuscript, rev. Apr. 18, 2011), 3.2, p. 7 (order on shadows pp. 6–7)

import Mathlib
import Definitions.Def_RobertsonSeymour2010_GM23_Immersion_QuasiOrders

namespace RobertsonSeymour2010.GM23.Immersion

theorem no_descending_shadows (X : Type) (Γ₁ Γ₂ : Set X) (hΓ : Disjoint Γ₁ Γ₂)
    (hΓ₁ : Γ₁.Infinite) (hΓ₂ : Γ₂.Infinite) (S : ℕ → Shadow X Γ₁ Γ₂) :
    ¬ ∀ i : ℕ, (S (i + 1)).Lt (S i) := by sorry

end RobertsonSeymour2010.GM23.Immersion
