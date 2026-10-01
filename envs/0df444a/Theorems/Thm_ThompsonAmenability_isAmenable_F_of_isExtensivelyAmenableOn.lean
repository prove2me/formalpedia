-- Prove2me | Theorems.Thm_ThompsonAmenability_isAmenable_F_of_isExtensivelyAmenableOn
-- name    : ThompsonAmenability.isAmenable_F_of_isExtensivelyAmenableOn
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-09-30T19:07:49.207345+00:00
-- url     : https://prove2.me/theorems/3fdc6fc2-d996-4ab9-8c39-9eac5878771f
-- title:
--   Chornyi Corollary 3, 'if' direction — if F's action on the dyadics is extensively amenable, F is amenable
-- statement:
--   Let $X$ be the set of dyadic rationals in $(0,1)$. If the action of Thompson's group $F$ on $X$ is
--   extensively amenable (`IsExtensivelyAmenableOn F UI X`: there is an $F$-invariant mean on the finite
--   subsets of $[0,1]$, concentrated on the finite subsets of $X$, giving full weight to the finite sets
--   containing any given finite $E_0 \subseteq X$), then $F$ is amenable (`Garrido.IsAmenable F`).
--
--   **Source.** Chornyi, p. 7, Corollary 3: “Thompson's group $F$ is amenable if and only if its action
--   on $X=\mathbb Z[\frac12]\cap(0,1)$ is extensively amenable.” This is the “if” direction, the
--   substantive one: Chornyi derives it from the criterion of Juschenko, Matte Bon, Monod and de la
--   Salle (arXiv:1503.04977) through a cocycle recording the slope changes of elements of $F$ at dyadic
--   breakpoints. The “only if” direction holds for every action of an amenable group.
--
--   **Formalization Note.** Chornyi defines an action of $G$ on $X$ to be extensively amenable when the
--   action of the lamplighter group $P_f(X) \rtimes G$ on $P_f(X)$, $(E, g)(F) = E \mathbin{\triangle} gF$, is
--   amenable (Definition 10, pp. 6–7). The statement uses the equivalent form of Juschenko, Matte Bon,
--   Monod and de la Salle (arXiv:1503.04977, Definition 1.1): a $G$-invariant mean on the finite subsets
--   of $X$ giving full weight, for each finite $E_0 \subseteq X$, to the finite sets containing $E_0$.
--   The two agree by Juschenko–Monod (Ann. of Math. (2) 178 (2013) 775–787, §3.1), as Juschenko, Matte Bon, Monod
--   and de la Salle record on p. 2.
--   Extensive amenability is stated for the action on $[0,1]$ relative to $X$,
--   as in the F-amenability mission's statement of Corollary 3
--   (`ThompsonAmenability.mapsTo_dyadic_and_isAmenable_F_iff_isExtensivelyAmenableOn`), which also records
--   that $F$ maps $X$ to itself.
-- source:
--   Chornyi, M., Superharmonic functions on the lamplighter graph of Thompson's group F (2019), https://arxiv.org/abs/1907.01440v1, p. 7, Corollary 3, the 'if' direction

import Definitions.Def_CannonFloydParry
import Definitions.Def_Garrido_Amenability
import Definitions.Def_ThompsonAmenability
import Mathlib

namespace ThompsonAmenability

theorem isAmenable_F_of_isExtensivelyAmenableOn
    (h : IsExtensivelyAmenableOn CannonFloydParry.F CannonFloydParry.UI
      {x : CannonFloydParry.UI | 0 < (x : ℝ) ∧ (x : ℝ) < 1 ∧ CannonFloydParry.IsDyadic x}) :
    Garrido.IsAmenable CannonFloydParry.F := by
  sorry

end ThompsonAmenability
