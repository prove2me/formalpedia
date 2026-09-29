-- Prove2me | Theorems.Thm_PinnedAsymmetryQ_asymmetry_indep_transverse
-- name    : PinnedAsymmetryQ.asymmetry_indep_transverse
-- status  : Proved
-- author  : @ShapeZero
-- created : 2026-09-24T04:26:52.725452+00:00
-- url     : https://prove2.me/theorems/c54267c0-87a2-4415-802d-ae6f1adc5117
-- title:
--   The asymmetry does not depend on the transverse wavenumbers
-- statement:
--   Let $q \ge 1$, $K, c, \beta$ real, and let $k, k' \in \mathbb{R}^q$ have the same axis-0 component, $k_0 = k'_0$. Then
--
--   $$
--   \omega(k) - \omega(\bar k) = \omega(k') - \omega(\bar{k'}).
--   $$
--
--   The asymmetry depends only on $k_0$: it is the same whatever the transverse components of the wavevector. This is the transverse-independence stated in the mission title.
-- source:
--   Shape Zero LLC, "Formal Proofs of the C1 Verification Package" (August 2026), §7, Theorem 7.1 (extended to q axes): https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ShapeZero_C1_Formal_Proofs.pdf ; corrected in "Errata — C1 Formal Proofs (Sections 3 and 6)", "Related: the pinned asymmetry (Section 7)": https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ERRATUM_Theorem_6.1.md

import Mathlib
import Definitions.Def_PinnedAsymmetryQ_omega

open Real BigOperators

namespace PinnedAsymmetryQ
theorem asymmetry_indep_transverse (q : ℕ) [NeZero q] (K c β : ℝ)
    (k k' : Fin q → ℝ) (h0 : k 0 = k' 0) :
    omega q K c β k - omega q K c β (flip0 q k)
      = omega q K c β k' - omega q K c β (flip0 q k') := by sorry
end PinnedAsymmetryQ
