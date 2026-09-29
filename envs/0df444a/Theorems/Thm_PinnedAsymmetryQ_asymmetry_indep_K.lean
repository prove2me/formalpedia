-- Prove2me | Theorems.Thm_PinnedAsymmetryQ_asymmetry_indep_K
-- name    : PinnedAsymmetryQ.asymmetry_indep_K
-- status  : Proved
-- author  : @ShapeZero
-- created : 2026-09-24T04:26:26.194198+00:00
-- url     : https://prove2.me/theorems/19da7ef9-7390-45fc-8a21-02e18dba1677
-- title:
--   The asymmetry is the same for any two stiffnesses $K_1$, $K_2$
-- statement:
--   Let $q \ge 1$, $K_1, K_2, c, \beta$ real and $k \in \mathbb{R}^q$. Writing $\omega_K$ for the frequency with stiffness $K$ and $\bar k$ for the reversal along axis 0,
--
--   $$
--   \omega_{K_1}(k) - \omega_{K_1}(\bar k) = \omega_{K_2}(k) - \omega_{K_2}(\bar k).
--   $$
--
--   This is the stiffness-independence stated in the mission title.
-- source:
--   Shape Zero LLC, "Formal Proofs of the C1 Verification Package" (August 2026), §7, Theorem 7.1 (extended to q axes): https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ShapeZero_C1_Formal_Proofs.pdf ; corrected in "Errata — C1 Formal Proofs (Sections 3 and 6)", "Related: the pinned asymmetry (Section 7)" (stiffness cancels): https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ERRATUM_Theorem_6.1.md

import Mathlib
import Definitions.Def_PinnedAsymmetryQ_omega

open Real BigOperators

namespace PinnedAsymmetryQ
theorem asymmetry_indep_K (q : ℕ) [NeZero q] (K₁ K₂ c β : ℝ) (k : Fin q → ℝ) :
    omega q K₁ c β k - omega q K₁ c β (flip0 q k)
      = omega q K₂ c β k - omega q K₂ c β (flip0 q k) := by sorry
end PinnedAsymmetryQ
