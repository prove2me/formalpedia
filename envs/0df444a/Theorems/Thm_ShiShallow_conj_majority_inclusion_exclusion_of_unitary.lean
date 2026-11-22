-- Prove2me | Theorems.Thm_ShiShallow_conj_majority_inclusion_exclusion_of_unitary
-- name    : ShiShallow.conj_majority_inclusion_exclusion_of_unitary
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-13T23:04:43.86732+00:00
-- url     : https://prove2.me/theorems/d839b732-8ccf-4f9b-aeab-481bc14da7a1
-- title:
--   Conjugation by a unitary distributes over the majority inclusion-exclusion combination
-- statement:
--   Conjugating the majority inclusion-exclusion combination of three operators by a unitary yields the same combination of the three conjugated operators. The only fact in play is that conjugation by a unitary is multiplicative, since the adjacent factors contribute the identity. Applied to the output projectors of a three-copy majority verifier, this converts the acceptance operator of the combined circuit into the majority combination of the three single-copy acceptance operators, which is the form the spectral argument requires.

import Definitions.Def_ShiShallow_Matrix

set_option autoImplicit false

namespace ShiShallow

theorem conj_majority_inclusion_exclusion_of_unitary {n : ℕ} (A P Q R : Op n)
    (hA : star A * A = (1 : Op n)) :
    star A * (P * Q + Q * R + R * P - 2 * (P * Q * R)) * A
      = (star A * P * A) * (star A * Q * A)
        + (star A * Q * A) * (star A * R * A)
        + (star A * R * A) * (star A * P * A)
        - 2 * ((star A * P * A) * (star A * Q * A) * (star A * R * A)) := by
  sorry

end ShiShallow
