-- Prove2me | Theorems.Thm_ThompsonAmenability_exists_const_forall_isFolner_le_card
-- name    : ThompsonAmenability.exists_const_forall_isFolner_le_card
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-09-30T18:44:40.346987+00:00
-- url     : https://prove2.me/theorems/914ccf9f-b840-4b55-b03b-f9c02f09b843
-- title:
--   Moore Theorem 1.1 — Følner sets of F have at least tower-many elements
-- statement:
--   For every finite symmetric generating set $\Gamma$ of Thompson's group $F$ there is a constant $C > 1$ such that, for every $n$, every finite set $A \subseteq F$ that is $C^{-n}$-Følner with respect to $\Gamma$ has at least $\exp_n(0)$ elements, where $\exp_0(n) = n$ and $\exp_{p+1}(n) = 2^{\exp_p(n)}$.
--
--   **Formalization Note.** Moore multiplies tree diagrams as "$f$ followed by $g$", so Moore's right translate $A\cdot\gamma$ is the left translate $\gamma A$ for the composition of maps used here. For a symmetric $\Gamma$ the two statements are equivalent, since $A \mapsto A^{-1}$ exchanges left and right translates and preserves $|A|$. The theorem assumes nothing about amenability; by Følner's criterion it says that if $F$ is amenable, its Følner function grows faster than any tower of exponentials.
-- source:
--   Moore, J. T., Fast growth in the Følner function for Thompson's group F, Groups Geom. Dyn. 7 (2013) 633–651, https://doi.org/10.4171/GGD/201 (arXiv:0905.1118v7, whose page numbers are used), p. 2, Theorem 1.1

import Mathlib
import Definitions.Def_CannonFloydParry
import Definitions.Def_ThompsonAmenability

namespace ThompsonAmenability

theorem exists_const_forall_isFolner_le_card (Γ : Finset CannonFloydParry.F) (hsymm : ∀ γ ∈ Γ, γ⁻¹ ∈ Γ)
    (hgen : Subgroup.closure (Γ : Set CannonFloydParry.F) = ⊤) :
    ∃ C : ℝ, 1 < C ∧ ∀ (n : ℕ) (A : Finset CannonFloydParry.F),
      IsFolner Γ A (C ^ (-(n : ℤ))) → towerExp n 0 ≤ A.card := by
  sorry

end ThompsonAmenability
