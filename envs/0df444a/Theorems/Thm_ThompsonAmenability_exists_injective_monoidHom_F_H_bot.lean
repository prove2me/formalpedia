-- Prove2me | Theorems.Thm_ThompsonAmenability_exists_injective_monoidHom_F_H_bot
-- name    : ThompsonAmenability.exists_injective_monoidHom_F_H_bot
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-30T18:52:52.980602+00:00
-- url     : https://prove2.me/theorems/75dabcd3-2d96-41d7-9707-7a1b14b6a14e
-- title:
--   Stankov, p. 2 — H(ℤ) contains a copy of Thompson's group F
-- statement:
--   There is an injective group homomorphism from Thompson's group $F$ into Monod's group $H(\mathbf Z)$ (`Monod.H ⊥`): the homeomorphisms of the line that are piecewise in $\mathrm{PSL}_2(\mathbf Z)$ with breakpoints at fixed points of hyperbolic elements of $\mathrm{PSL}_2(\mathbf Z)$.
--
--   **Formalization Note.** `⊥` is the smallest subring of $\mathbf R$, the image of $\mathbf Z$. A subgroup of an amenable group is amenable, so with this statement, if $H(\mathbf Z)$ is amenable then so is $F$.
-- source:
--   Stankov, B., Non-triviality of the Poisson boundary of random walks on the group H(Z) of Monod, Ergodic Theory Dynam. Systems 41 (2021) 1160–1189, https://doi.org/10.1017/etds.2019.76 (arXiv:1806.00301, whose page numbers are used), p. 2, §1

import Mathlib
import Definitions.Def_CannonFloydParry
import Definitions.Def_Monod_PiecewiseProjective

namespace ThompsonAmenability

theorem exists_injective_monoidHom_F_H_bot :
    ∃ φ : CannonFloydParry.F →* Monod.H ⊥, Function.Injective φ := by
  sorry

end ThompsonAmenability
