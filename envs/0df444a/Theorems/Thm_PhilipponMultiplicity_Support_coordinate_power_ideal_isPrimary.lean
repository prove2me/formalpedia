-- Prove2me | Theorems.Thm_PhilipponMultiplicity_Support_coordinate_power_ideal_isPrimary
-- name    : PhilipponMultiplicity.Support.coordinate_power_ideal_isPrimary
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-30T12:12:48.10193+00:00
-- url     : https://prove2.me/theorems/507b8d6c-940a-49e7-8352-1d16cd2edf88
-- title:
--   Positive coordinate-power ideals over a field are primary
-- statement:
--   Let $K$ be a field, let $\sigma$ be a finite set of variables, and let $S\subseteq\sigma$. Assign a positive integer $n_i$ to each $i\in S$. In the polynomial ring $R=K[X_i:i\in\sigma]$, the ideal
--
--   $$Q=(X_i^{n_i}:i\in S)$$
--
--   is primary: it is proper, and whenever $fg\in Q$ with $f\notin Q$, some positive power of $g$ lies in $Q$.
--
--   The empty set $S$ is allowed, in which case $Q=(0)$ in a polynomial ring over a field. Values of $n_i$ outside $S$ are irrelevant.
--
--   This gives primary components for monomial decompositions and supplies the algebraic input for the two section components in Philippon's example.
--
--   **Formalization Note.** This is the field-independent form of Hoşten–Smith, Lemma 2.1(1), which is printed over $\mathbb Q$. It has no Philippon-specific hypotheses. The intersection, radicals, minimal primes, Hilbert polynomials, and reduction of the canonical component sum are proved separately in the parent submission.
-- source:
--   S. Hoşten and G. G. Smith, Monomial Ideals, §2, Lemma 2.1(1), chapter p. 6, https://macaulay2.com/Book/ComputationsBook/chapters/monomialIdeals/chapter-wrapper.pdf . The cited version uses Q; this is its field-independent generalization, with the Artinian-local quotient and polynomial-extension argument explained in the parent submission. Application: Philippon (1986), Section 3, pp. 370–371, https://numdam.org/articles/10.24033/bsmf.2060/ .

import Mathlib

set_option autoImplicit false

namespace PhilipponMultiplicity.Support

universe u v

theorem coordinate_power_ideal_isPrimary
    (K : Type u) [Field K] (σ : Type v) [Finite σ]
    (S : Set σ) (n : σ → ℕ) (hn : ∀ i ∈ S, 0 < n i) :
    (Ideal.span ((fun i => (MvPolynomial.X i : MvPolynomial σ K) ^ n i) '' S)).IsPrimary := by sorry

end PhilipponMultiplicity.Support
