-- Prove2me | Theorems.Thm_PhilipponMultiplicity_product_projective_hilbert_function
-- name    : PhilipponMultiplicity.product_projective_hilbert_function
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-25T18:18:38.2306+00:00
-- url     : https://prove2.me/theorems/256c0b81-56ad-450b-9b9c-2889abe463e0
-- title:
--   Exact quotient Hilbert function of a projective product
-- statement:
--   Let $V_i$ be locally closed subsets of projective spaces over a field. At every natural multidegree, including zero degrees,
--   $$
--   h_{V_1\times\cdots\times V_p}(d_1,\ldots,d_p)=\prod_i h_{V_i}(d_i).
--   $$
--   Here each Hilbert function is the dimension of the image of the homogeneous polynomial piece in the actual coordinate-ring quotient by the vanishing ideal. Empty factors are allowed. This identity precedes any assertion that the Hilbert functions are eventually polynomial.
-- source:
--   Philippon, Lemmes de zéros dans les groupes algébriques commutatifs (1986), https://numdam.org/articles/10.24033/bsmf.2060/, §3 pp. 361–362 and Lemma 3.4 p. 371. Supporting algebra for the numbered result; the paper itself uses the geometric interpretation of the mixed coefficients.

import Definitions.Def_PhilipponMultiplicity_SectionThree

set_option autoImplicit false
open scoped BigOperators
open PhilipponMultiplicity PhilipponMultiplicity.SectionThree

theorem PhilipponMultiplicity.product_projective_hilbert_function (K : Type*) [Field K]
    (M : MultiProjectiveSpace K)
    (V : ∀ i : M.FactorIndex, ProjectiveSubvariety K (M.ambientDimension i))
    (d : M.FactorIndex → ℕ) :
    Hilbert.hilbertFunction K M.factorCount M.ambientDimension
      (M.vanishingIdeal (productCarrier M V)) d =
      ∏ i, Hilbert.hilbertFunction K 1 (fun _ => M.ambientDimension i)
        ((projectiveSpace K (M.ambientDimension i)).vanishingIdeal
          (V i).carrierInSingleFactor) (fun _ => d i) := by sorry
