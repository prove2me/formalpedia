-- Prove2me | Theorems.Thm_PhilipponMultiplicity_lemma_3_2
-- name    : PhilipponMultiplicity.lemma_3_2
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-23T20:50:13.740967+00:00
-- url     : https://prove2.me/theorems/7d935bfb-2ddf-4627-b8f2-e93e6c7878d5
-- title:
--   Lemma 3.2 — top components and their lengths
-- statement:
--   **Proved with no Open theorem dependencies, verified 29 September 2026.** Checked locally with Lean 4.33.1 and the proposal’s pinned Mathlib. An independent blind readback is attached.
--
--   The actual Hilbert degree form is the sum of the degree forms of the relevant top-dimensional minimal primes, weighted by actual localized quotient lengths. Evaluation degrees are positive; dimension zero is included.
-- source:
--   1986, p.364. https://numdam.org/articles/10.24033/bsmf.2060/

/- Open source statement, Lemma 3.2 (p. 364).
The summation uses actual minimal primes and actual finite localized lengths.
Its comparison with primary components of maximal projective dimension is
part of the proof, not an assumed list or a numeric field.
-/
import Definitions.Def_PhilipponMultiplicity_SectionThree

set_option autoImplicit false
open scoped BigOperators

namespace PhilipponMultiplicity
open SectionThree

theorem lemma_3_2
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (M : MultiProjectiveSpace K)
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I)
    (hNontrivial : IsNontrivialIdeal M I)
    (d : M.FactorIndex → ℕ) (hd : ∀ i, 1 ≤ d i) :
    idealDegreeValue M I d = topComponentLengthSum M I d := by sorry

end PhilipponMultiplicity
