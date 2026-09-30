-- Prove2me | Theorems.Thm_TranscendenceTheory_finite_quotient_multiplicity_model
-- name    : TranscendenceTheory.finite_quotient_multiplicity_model
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-21T01:06:24.696089+00:00
-- url     : https://prove2.me/theorems/f8ec54ec-9bd1-47ac-a98b-ffc0657b2553
-- title:
--   Finite quotient models preserve local multiplicities exactly
-- statement:
--   Let $R$ be a commutative complex algebra, and let $I$ be an ideal such that $R/I$ is finite-dimensional over $\mathbb C$. Let $Y$ be an indexing set, and let $p:Y\to\operatorname{Spec}(R)$ be injective with $I\subseteq p(c)$ for every $c\in Y$.
--
--   There exists a finite complex algebra multiplicity model $M$ on $Y$ whose algebra has dimension
--
--   $$\dim_{\mathbb C}M.A=\dim_{\mathbb C}(R/I),$$
--
--   and whose local multiplicity at each index is exactly
--
--   $$M.e_c=\ell_{R_{p(c)}}\bigl(R_{p(c)}/IR_{p(c)}\bigr).$$
--
--   Every displayed localized quotient length is finite. The construction uses the algebra $R/I$ and the distinct quotient primes $p(c)/I$, so it loses neither multiplicity nor dimension. No Noetherian hypothesis on $R$ is required.
--
--   This connects localized ideal multiplicities in a coordinate ring to the local factors of a finite algebra. In the Weierstrass application, one must still choose a suitable ideal containing the chart cubic, compare the derivative-ideal budgets with these multiplicities, and bound the quotient dimension. Empty indexing sets and the zero quotient are included.
--
--   **Formalization Note** The model's multiplicities are natural numbers; the theorem proves that the original extended natural lengths are finite as well as identifying their natural-number values.
-- source:
--   Stacks Project, Proposition 10.9.14 (tag 00CT), https://stacks.math.columbia.edu/tag/00CT: localization commutes with quotient; Lemma 10.52.3 (tag 00IV), https://stacks.math.columbia.edu/tag/00IV: length additivity; the quotient ideal correspondence preserves submodule lattices and module length under surjective scalar restriction. Given a finite complex quotient R/I and distinct support primes p_i containing I, the complete theorem constructs the finite algebra model A=R/I, preserves finrank exactly, and identifies each localization length with length over R_(p_i) of R_(p_i)/IR_(p_i). The new geometric child specializes R to C[t,x,y,u], requires I to contain the first Weierstrass cubic, and retains the chart-budget and uniform section-dimension obligations. It is a sufficient first-chart finite-quotient route, not a formalized converse or a claim that slicing has been constructed. Multiplicities in the source zero-estimate framework: Philippon (1986), section 3, Lemma 3.2, p. 364, https://www.numdam.org/item/10.24033/bsmf.2060.pdf. Application: Senthil Kumar K (2026), Appendix A, Theorem A.2, https://doi.org/10.1017/S001309152610145X.

import Definitions.Def_TranscendenceTheory_FiniteAlgebraMultiplicityModel
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Ideal.Quotient.Operations

theorem TranscendenceTheory.finite_quotient_multiplicity_model
    (R : Type) [CommRing R] [Algebra ℂ R] (I : Ideal R)
    [Module.Finite ℂ (R ⧸ I)] (ι : Type) (p : ι → PrimeSpectrum R)
    (hp : Function.Injective p) (hIp : ∀ i, I ≤ (p i).asIdeal) :
    ∃ M : FiniteAlgebraMultiplicityModel ι,
      Module.finrank ℂ M.A = Module.finrank ℂ (R ⧸ I) ∧
      ∀ i, M.localLength i =
        (Module.length (Localization.AtPrime (p i).asIdeal)
          ((Localization.AtPrime (p i).asIdeal) ⧸ I.map
            (algebraMap R (Localization.AtPrime (p i).asIdeal)))).toNat ∧
        Module.length (Localization.AtPrime (p i).asIdeal)
          ((Localization.AtPrime (p i).asIdeal) ⧸ I.map
            (algebraMap R (Localization.AtPrime (p i).asIdeal))) ≠ ⊤ := by sorry
