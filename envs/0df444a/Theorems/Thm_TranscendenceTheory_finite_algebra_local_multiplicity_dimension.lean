-- Prove2me | Theorems.Thm_TranscendenceTheory_finite_algebra_local_multiplicity_dimension
-- name    : TranscendenceTheory.finite_algebra_local_multiplicity_dimension
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-21T00:36:29.362996+00:00
-- url     : https://prove2.me/theorems/5db538fd-0b38-451e-b2db-ffec33a196f1
-- title:
--   Local multiplicities and dimension of a finite algebra
-- statement:
--   Let $K$ be an algebraically closed field and let $A$ be a finite-dimensional commutative $K$-algebra. Every prime localization $A_{\mathfrak p}$ has finite module length. If $I$ is a finite set and $p:I\to\operatorname{Spec}(A)$ is injective, then
--
--   $$\sum_{i\in I}\ell_{A_{p(i)}}(A_{p(i)})\leq\dim_K A.$$
--
--   If $p$ is also surjective, equality holds:
--
--   $$\sum_{i\in I}\ell_{A_{p(i)}}(A_{p(i)})=\dim_K A.$$
--
--   This is the multiplicity-dimension relation for a finite algebra, including nonreduced algebras. The injectivity assumption prevents counting the same local factor more than once. The empty family and the zero algebra are included. In applications to a zero estimate, one must still construct the finite algebra and compare its dimension with the relevant bounded-degree section space.
--
--   **Formalization Note** The statement proves that all extended natural local lengths are finite before summing their natural-number values. It does not identify the positive-dimensional Weierstrass chart ring itself as a finite-dimensional complex algebra.
-- source:
--   Stacks Project, Lemma 10.53.5 (tag 00JA) and Lemma 10.53.6 (tag 00JB), https://stacks.math.columbia.edu/tag/00JA and https://stacks.math.columbia.edu/tag/00JB: Artinian decomposition into prime localizations; Lemma 10.52.3 (tag 00IV), https://stacks.math.columbia.edu/tag/00IV: additivity of module length. For a finite algebra over an algebraically closed field, the residue fields have degree one, so the local lengths sum exactly to the vector-space dimension. An injectively indexed subfamily has no greater sum. This is the finite-algebra, dimension-zero supporting case of the multiplicity relation in Philippon (1986), section 3, Lemma 3.2, p. 364, https://www.numdam.org/item/10.24033/bsmf.2060.pdf. The frontier child asks for a finite complex algebra realizing the chart multiplicity budgets at distinct primes, with its dimension bounded by the relevant section-space dimension. This is a sufficient finite-model route, not a quotation or proof of the full Lemma 3.2. Locus selection, finite-algebra realization, local-length comparisons and the uniform section-degree bound remain required. Application: Senthil Kumar K (2026), Appendix A, Theorem A.2, https://doi.org/10.1017/S001309152610145X.

import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.RingTheory.Length
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.RingTheory.LocalRing.Length
import Mathlib.FieldTheory.IsAlgClosed.Basic

theorem TranscendenceTheory.finite_algebra_local_multiplicity_dimension
    (K A : Type*) [Field K] [IsAlgClosed K] [CommRing A] [Algebra K A]
    [Module.Finite K A] :
    (∀ p : PrimeSpectrum A,
      Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal) ≠ ⊤) ∧
    ∀ (ι : Type*) [Fintype ι] (p : ι → PrimeSpectrum A), Function.Injective p →
      (∑ i, (Module.length (Localization.AtPrime (p i).asIdeal)
        (Localization.AtPrime (p i).asIdeal)).toNat) ≤ Module.finrank K A ∧
      (Function.Surjective p →
        (∑ i, (Module.length (Localization.AtPrime (p i).asIdeal)
          (Localization.AtPrime (p i).asIdeal)).toNat) = Module.finrank K A) := by sorry
