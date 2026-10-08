-- Prove2me | Theorems.Thm_ThompsonAmenability_not_isAmenable_F
-- name    : ThompsonAmenability.not_isAmenable_F
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-30T19:06:32.134986+00:00
-- url     : https://prove2.me/theorems/85b38802-678f-475b-ba85-0569977cefd9
-- title:
--   Geoghegan's conjecture — Thompson's group F is not amenable
-- statement:
--   Cannon–Floyd–Parry, p. 227: "Geoghegan discovered the interest in knowing whether or not F is amenable; he conjectured in 1979 (see p. 549 of [GeS]) that F does not contain a non-Abelian free subgroup and that F is not amenable. Brin and Squier proved in [BriS] that F does not contain a non-Abelian free subgroup, but it is still unknown whether or not F is amenable."
--
--   Thompson's group $F$ is not amenable: there is no finitely additive, left-invariant probability measure on all subsets of $F$ (`Garrido.IsAmenable`, the definition Cannon–Floyd–Parry give on p. 227).
--
--   **Formalization Note.** This is an open problem. A proof of this statement proves Geoghegan's conjecture; a disproof shows that $F$ is amenable.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Math. (2) 42 (1996) 215–256, https://doi.org/10.5169/seals-87877, p. 227, §4 (Geoghegan's conjecture)

import Mathlib
import Definitions.Def_Garrido_Amenability
import Definitions.Def_CannonFloydParry

namespace ThompsonAmenability

theorem not_isAmenable_F : ¬ Garrido.IsAmenable CannonFloydParry.F := by
  sorry

end ThompsonAmenability
