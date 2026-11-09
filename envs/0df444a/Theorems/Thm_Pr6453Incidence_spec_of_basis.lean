-- Prove2me | Theorems.Thm_Pr6453Incidence_spec_of_basis
-- name    : Pr6453Incidence.spec_of_basis
-- status  : Proved
-- author  : @gustasmickus
-- created : 2026-11-08T22:50:02.907207+00:00
-- url     : https://prove2.me/theorems/8ed4df44-6789-4bf9-9853-b219de3610b0
-- title:
--   PR #6453: checking the incidence on basis pairs suffices
-- statement:
--   The finite verification principle for the incidence of a word.
--
--   The incidence is the data that says which input rows carry the coefficients of the first multiplicand and which carry those of the second (`enc`), how the target rows are read as CRT coordinates (`read`), and what the product is in those coordinates (`P`). The word acts by a linear map $M$ on its rows. All four maps are linear in each slot, so if the word produces the right answer on the basis pairs — $\mathrm{enc}(e_i, e_j)$ for all $i, j$ — then it produces it on every pair of coefficient vectors.
--
--   This is what makes an incidence checkable: for a word with 1152 polynomial coefficients it reduces the specification to 1152 x 1152 basis inputs. What it does not do is exhibit the incidence of a particular word — the certificate records the shape of the module but not which column carries which coefficient.
-- source:
--   CrocSwap/integer-mult-bounds, PR #6453, head b1a3e525793eca35c56324aa7ffd0b714cf606d4, RESULT.json (module block: six fields, four Gaussian characters, 1152 polynomial coefficients).

import Mathlib

set_option autoImplicit false

namespace Pr6453Incidence

theorem spec_of_basis {ι κ n : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [Fintype n]
    (enc : (ι → ℚ) →ₗ[ℚ] (ι → ℚ) →ₗ[ℚ] (n → ℚ))
    (M : (n → ℚ) →ₗ[ℚ] (n → ℚ))
    (read : (n → ℚ) →ₗ[ℚ] (κ → ℚ))
    (P : (ι → ℚ) →ₗ[ℚ] (ι → ℚ) →ₗ[ℚ] (κ → ℚ))
    (hbasis : ∀ i j, read (M (enc (Pi.single i 1) (Pi.single j 1))) =
      P (Pi.single i 1) (Pi.single j 1)) :
    ∀ a b : ι → ℚ, read (M (enc a b)) = P a b := by
  sorry

end Pr6453Incidence
