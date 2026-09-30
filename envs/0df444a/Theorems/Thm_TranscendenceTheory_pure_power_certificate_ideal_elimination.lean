-- Prove2me | Theorems.Thm_TranscendenceTheory_pure_power_certificate_ideal_elimination
-- name    : TranscendenceTheory.pure_power_certificate_ideal_elimination
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-22T02:45:22.493428+00:00
-- url     : https://prove2.me/theorems/f8c55772-7770-4174-b21c-a2907c0a1707
-- title:
--   Eliminating auxiliary ideals from pure-power multiplicity certificates
-- statement:
--   Let K be an algebraically closed field and R = K[x_i : i in σ], with σ finite. Fix a monomial order, nonnegative exponents d_i, and polynomials b_i having unit leading coefficients and pure-power leading exponent vectors d_i e_i. Write J = (b_i).
--
--   Then R/J is finite-dimensional, with dimension at most product_i d_i. Its local lengths are finite, and their sum over any finite family of distinct primes is at most the same product.
--
--   For every finite label set and prescribed nonnegative integer budgets e_j, the following conditions are equivalent:
--
--   1. There exists an ideal I containing every b_i, and a distinct prime of R/I for each label, whose local length is at least the corresponding e_j.
--   2. There exists a distinct prime of R/J for each label, whose local length is at least the corresponding e_j.
--
--   Thus no separate auxiliary ideal is needed. The equivalence fixes the polynomials, leading exponents, monomial order and label set. It preserves all lower budgets and the exponent-product upper bound. The ideal and selected primes may change, and equality of the individual local lengths is not asserted. Nonradical ideals, zero exponents and empty label sets are included.
-- source:
--   Derived ideal-elimination lemma for A.1 pure-power certificates. The map R/(b_i) -> R/I is surjective whenever each b_i belongs to I. Its maps on prime localizations are surjective, so local module lengths cannot increase after passing to R/I. This follows from the localization map and length APIs in pinned Mathlib: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/Localization/AtPrime/Basic.lean and https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/Length.lean. The existing Proved pure-power bound https://prove2.me/theorems/e9388901-0807-47a0-a199-355c708a5ad9 bounds the generated quotient and its total local multiplicities by the same exponent product. The source relation is a supporting zero-dimensional ideal-monotonicity step for the global multiplicity argument of Philippon (1986), section 3, https://www.numdam.org/item/10.24033/bsmf.2060.pdf. No full multihomogeneous Bezout result is claimed. Both frontier directions preserve C, the four polynomials, their exponents and monomial order, the locus and chart point, and all lower budgets. The auxiliary ideal and primes can change. Selecting the four equations and proving the uniform bidegree product bound remain Open.

import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.RingTheory.LocalRing.Length
import Mathlib.FieldTheory.IsAlgClosed.Basic


import Mathlib.RingTheory.Spectrum.Prime.RingHom

theorem TranscendenceTheory.pure_power_certificate_ideal_elimination
    (K : Type*) [Field K] [IsAlgClosed K] (σ : Type*) [Fintype σ]
    (o : MonomialOrder σ) (d : σ → ℕ) (b : σ → MvPolynomial σ K)
    (hu : ∀ i, IsUnit (o.leadingCoeff (b i)))
    (hd : ∀ i, o.degree (b i) = Finsupp.single i (d i)) :
    let J : Ideal (MvPolynomial σ K) := Ideal.span (Set.range b)
    Module.Finite K (MvPolynomial σ K ⧸ J) ∧
      Module.finrank K (MvPolynomial σ K ⧸ J) ≤ ∏ i, d i ∧
      (∀ p : PrimeSpectrum (MvPolynomial σ K ⧸ J),
        Module.length (Localization.AtPrime p.asIdeal)
          (Localization.AtPrime p.asIdeal) ≠ ⊤) ∧
      (∀ (ι : Type*) [Fintype ι]
        (p : ι → PrimeSpectrum (MvPolynomial σ K ⧸ J)), Function.Injective p →
        (∑ i, (Module.length (Localization.AtPrime (p i).asIdeal)
          (Localization.AtPrime (p i).asIdeal)).toNat) ≤ ∏ i, d i) ∧
      ∀ (ι : Type*) [Fintype ι] (e : ι → ℕ),
        (∃ I : Ideal (MvPolynomial σ K), (∀ i, b i ∈ I) ∧
          ∃ p : ι → PrimeSpectrum (MvPolynomial σ K ⧸ I),
            Function.Injective p ∧ ∀ i, e i ≤
              (Module.length (Localization.AtPrime (p i).asIdeal)
                (Localization.AtPrime (p i).asIdeal)).toNat) ↔
        ∃ q : ι → PrimeSpectrum (MvPolynomial σ K ⧸ J),
          Function.Injective q ∧ ∀ i, e i ≤
            (Module.length (Localization.AtPrime (q i).asIdeal)
              (Localization.AtPrime (q i).asIdeal)).toNat := by sorry
