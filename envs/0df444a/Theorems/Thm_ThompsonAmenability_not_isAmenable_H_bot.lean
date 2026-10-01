-- Prove2me | Theorems.Thm_ThompsonAmenability_not_isAmenable_H_bot
-- name    : ThompsonAmenability.not_isAmenable_H_bot
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-09-30T18:57:36.207706+00:00
-- url     : https://prove2.me/theorems/2c37d11c-772a-46f1-856a-3f0a903b2a38
-- title:
--   Monod, Problem 12 — H(ℤ) is not amenable (open)
-- statement:
--   Monod's group $H(\mathbf Z)$ (`Monod.H ⊥`) is not amenable.
--
--   **Formalization Note.** Monod asks "Is H(Z) amenable?" without conjecturing an answer; the statement takes the non-amenable side, parallel to Geoghegan's conjecture for $F$. The question is open. Since $F$ embeds in $H(\mathbf Z)$ (Stankov), a proof of Geoghegan's conjecture proves this statement, and a disproof of this statement disproves Geoghegan's conjecture.
-- source:
--   Monod, N., Groups of piecewise projective homeomorphisms, Proc. Natl. Acad. Sci. USA 110 (2013) 4524–4527, https://doi.org/10.1073/pnas.1218426110 (arXiv:1209.5229v2, whose page numbers are used), p. 2, Problem 12

import Mathlib
import Definitions.Def_Garrido_Amenability
import Definitions.Def_Monod_PiecewiseProjective

namespace ThompsonAmenability

theorem not_isAmenable_H_bot : ¬ Garrido.IsAmenable (Monod.H ⊥) := by
  sorry

end ThompsonAmenability
