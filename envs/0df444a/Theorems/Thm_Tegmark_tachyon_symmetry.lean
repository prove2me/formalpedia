-- Prove2me | Theorems.Thm_Tegmark_tachyon_symmetry
-- name    : Tegmark.tachyon_symmetry
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-21T04:15:23.700028+00:00
-- url     : https://prove2.me/theorems/c6e8d57f-b9f3-44c5-aaaf-107feab2d54e
-- title:
--   A mere minus sign: the classification is symmetric in space and time
-- statement:
--   The letter's page L74: since a mere minus sign distinguishes space from time, the remaining case (n, m) = (1, 3) is mathematically equivalent to the case (n, m) = (3, 1) in which all particles are tachyons (Feinberg 1967). The theorem captures the symmetry at the level of the classification: the class of the field equations of an (n, m) world is the class of an (m, n) world. Together with the data-surface milestones, this is why the tachyon-symmetric worlds fail the predictability requirement exactly as the multi-time worlds do.
--
--   **Formalization Note** The statement is the symmetry of the classifier; the tachyon reading (imaginary rest mass, well-posed problems requiring data outside the lightcones) is the letter's physical interpretation and is not formalized.
-- source:
--   M. Tegmark, On the dimensionality of spacetime, Class. Quantum Grav. 14 (1997) L69-L75, p. L74 (citing Feinberg 1967).

import Mathlib
import Definitions.Def_Tegmark_sig
import Definitions.Def_Tegmark_phys
import Definitions.Def_Tegmark_ensemble

namespace Tegmark

/-!
# A mere minus sign: the space-time symmetry

The classification of the field equations is unchanged under the
exchange of the numbers of space and time dimensions, because a
single minus sign distinguishes space from time (Tegmark 1997,
p. L74). The "(1, 3)" world of tachyons is, at the level of the
classification, mathematically equivalent to the "(3, 1)" world.
-/

/-- The classification of the field equations is symmetric under
the exchange of the numbers of space and time dimensions (Tegmark
1997, p. L74): the class of an "(n, m)" world is the class of an
"(m, n)" world. -/
theorem tachyon_symmetry (n m : ℕ) : pdeClass n m = pdeClass m n := by
  sorry

end Tegmark
