-- Prove2me | Theorems.Thm_ShiShallow_mulVec_majority_inclusion_exclusion_of_common_eigenvector
-- name    : ShiShallow.mulVec_majority_inclusion_exclusion_of_common_eigenvector
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-13T20:15:21.808763+00:00
-- url     : https://prove2.me/theorems/ddecef31-a583-404a-95d7-3cd4cae8ca8f
-- title:
--   Majority inclusion-exclusion polynomial acts diagonally on a common eigenvector
-- statement:
--   If a vector φ is a common eigenvector of three operators A, B, C with eigenvalues α, β, γ, then the majority-of-three inclusion-exclusion combination AB + BC + CA - 2ABC sends φ to (αβ + βγ + γα - 2αβγ)·φ. This is the operator form of maj(p) = 3p² - 2p³ restricted to a common eigenvector.

import Definitions.Def_ShiShallow_Matrix

set_option autoImplicit false

namespace ShiShallow

theorem mulVec_majority_inclusion_exclusion_of_common_eigenvector {n : ℕ}
    (A B C : Op n) (φ : Bits n → ℂ) (α β γ : ℂ)
    (hA : Matrix.mulVec A φ = α • φ) (hB : Matrix.mulVec B φ = β • φ)
    (hC : Matrix.mulVec C φ = γ • φ) :
    Matrix.mulVec (A * B + B * C + C * A - (2 : ℂ) • (A * B * C)) φ
      = (α * β + β * γ + γ * α - 2 * (α * β * γ)) • φ := by
  sorry

end ShiShallow
