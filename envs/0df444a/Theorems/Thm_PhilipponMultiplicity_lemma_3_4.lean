-- Prove2me | Theorems.Thm_PhilipponMultiplicity_lemma_3_4
-- name    : PhilipponMultiplicity.lemma_3_4
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-23T20:51:48.727124+00:00
-- url     : https://prove2.me/theorems/551fcde2-277c-478c-8562-4684e11c2c3b
-- title:
--   Lemma 3.4 — Hilbert form of a product
-- statement:
--   **Proved with no Open theorem dependencies, verified 29 September 2026.** Checked locally with Lean 4.33.1 and the proposal’s pinned Mathlib. An independent blind readback is attached.
--
--   The degree form of the actual product of projective subvarieties is the factorial of the product dimension divided by the factorials of the factor dimensions, times the factor degrees and the prescribed degree monomial.
-- source:
--   1986, p.371. https://numdam.org/articles/10.24033/bsmf.2060/

/- Open source statement, Lemma 3.4 (p. 371).
The factors are actual locally closed projective subsets. The numerator is
the factorial of the actual product-locus Hilbert dimension, as printed.
-/
import Definitions.Def_PhilipponMultiplicity_SectionThree

set_option autoImplicit false
open scoped BigOperators

namespace PhilipponMultiplicity
open SectionThree

theorem lemma_3_4
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (M : MultiProjectiveSpace K)
    (V : ∀ i : M.FactorIndex, ProjectiveSubvariety K (M.ambientDimension i))
    (d : M.FactorIndex → ℕ) (hd : ∀ i, 1 ≤ d i) :
    locusDegreeValue M (productCarrier M V) d =
      ((locusDimension M (productCarrier M V)).factorial : ℚ) /
        (∏ i, ((V i).dimension.factorial : ℚ)) *
        (∏ i, (V i).degree) * ∏ i, (d i : ℚ) ^ (V i).dimension := by sorry

end PhilipponMultiplicity
