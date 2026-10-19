-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P10_povm_radonNikodym
-- name    : QAlgorithms.Papers.Independent.Frontier30.P10.povm_radonNikodym
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:14:05.247985+00:00
-- url     : https://prove2.me/theorems/d2e0c078-0c5c-445b-9746-593055f5e9ad
-- title:
--   Radon–Nikodym representation of a POVM
-- statement:
--   Let $\mathcal H$ be a separable complex Hilbert space, $X$ a complete separable metric space with its Borel sets, and $M$ a normalized positive operator-valued measure on $X$. There are a positive sigma-finite measure $\mu$, a dense complex linear domain $D\subseteq\mathcal H$, and a countable family of measurable algebraic linear functionals $a_k(x):D\to\mathbb C$ such that, for every $\psi\in D$ and Borel set $S\subseteq X$,
--
--   $$
--   \int_X\sum_{k=0}^{\infty}|a_k(x)\psi|^2\,\mu(dx)=\|\psi\|^2,
--   \qquad
--   \langle\psi,M(S)\psi\rangle=\int_S\sum_{k=0}^{\infty}|a_k(x)\psi|^2\,\mu(dx).
--   $$
--
--   The functionals need not be bounded or continuous on $D$. Their linear versions can be chosen everywhere by modifying a null set. This representation applies to arbitrary POVMs, including those without bounded operator densities.
--
--   **Formalization Note** The nonnegative integrals and series take values in $[0,\infty]$; their finite values are conclusions, so no divergent real series is replaced by its default value.
-- source:
--   Entanglement-breaking channels in infinite dimensions, arXiv:0802.0235v1, PDF p. 3, Lemma 1: Radon–Nikodym representation of a POVM (9)–(10)

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P10

noncomputable section

open MeasureTheory

open scoped ENNReal ComplexOrder

namespace QAlgorithms.Papers.Independent.Frontier30.P10

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Holevo, arXiv:0802.0235v1, PDF pp.3–5, Lemma 1, (9)–(10).
Nonnegative integrals and sums are in ENNReal, retaining possible pointwise
infinity on null sets. The functionals are algebraic on the dense domain;
no continuity, boundedness, finite-rank or finite-energy hypothesis is imposed. -/
theorem povm_radonNikodym [SecondCountableTopology H]
    {X : Type*} [MetricSpace X] [CompleteSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] (M : HilbertPOVM H X) :
    ∃ (mu : Measure X) (_hmu : SigmaFinite mu) (D : Submodule ℂ H),
      Dense (D : Set H) ∧
      ∃ a : X → ℕ → (D →ₗ[ℂ] ℂ),
        (∀ k u, AEMeasurable (fun x => a x k u) mu) ∧
        (∀ u : D, (∫⁻ x, ∑' k : ℕ, ENNReal.ofReal (‖a x k u‖ ^ 2) ∂mu) =
          ENNReal.ofReal (‖(u : H)‖ ^ 2)) ∧
        (∀ (S : Set X), MeasurableSet S → ∀ u : D,
          M.law (u : H) S =
            ∫⁻ x in S, ∑' k : ℕ, ENNReal.ofReal (‖a x k u‖ ^ 2) ∂mu) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P10

end
