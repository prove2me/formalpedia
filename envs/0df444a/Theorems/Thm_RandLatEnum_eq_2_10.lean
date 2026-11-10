-- Prove2me | Theorems.Thm_RandLatEnum_eq_2_10
-- name    : RandLatEnum.eq_2_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:14:45.250194+00:00
-- url     : https://prove2.me/theorems/07f976de-15f0-4ae1-8ecd-96b95c06353d
-- title:
--   Eq. (2.10) — Poisson $\rho(L)=\rho(L^*)/\det L$ and Siegel $\mathbb E_{\mu_n}[\rho(L)]=2$
-- statement:
--   Let $\rho(L)=\sum_{v\in L}e^{-\pi\|v\|^2}$ be the Gaussian mass. Then:
--
--   1. (Poisson summation) for every lattice $L$, with $L^*$ its dual in its span and $\det L$ its covolume in its span,
--   $$
--   \rho(L)=\frac{\rho(L^*)}{\det L};
--   $$
--   2. (Siegel's mean-value formula, zero vector included) for $n\ge2$ and $L\sim\mu_n$,
--   $$
--   \mathbb E_{\mu_n}[\rho(L)]=2 .
--   $$
--
--   The two identities give the upper bound on the level counts $N_d(B,\lambda_1)$ in Proposition 3.1.
--
--   **Formalization Note** The first identity is stated for the span of any linearly independent family in any $\mathbb R^k$, as the paper applies it to projected lattices. The Gaussian mass takes values in $[0,\infty]$; the defining sum is the definition `rhoL` and is not a clause.
--
--   Differences from the source:
--   - encoding: a lattice L in its span, det L, L* → the ℤ-span of a linearly independent b : Fin d → ℝᵏ, det = product of Gram–Schmidt lengths, L* = dual in the real span; reason: standard representation; the same lattices and quantities
--   - encoding: ρ(L) as a real sum → a sum of nonnegative terms in [0, ∞]; reason: the sums converge for lattices, so the values agree
--   - encoding: the Haar probability measure µ_n on X_n → any SL_n(ℝ)-invariant Borel probability measure on X_n, taken as a hypothesis; reason: X_n has exactly one such measure (Siegel), so the instances are the same; Mathlib does not construct it
--   - encoding: the expectation E_{µ_n} → the lower Lebesgue integral ∫⁻ of the [0,∞]-valued integrand; reason: the integrand is nonnegative and measurable (p.14); for measurable integrands ∫⁻ is the expectation
-- source:
--   Laarhoven, Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices, arXiv:2610.15265 (held version, sha256 8fa7a08a…), §2.3, (2.10), p.16

import Mathlib
import Definitions.Def_KannanLattice_Core_Lattice
import Definitions.Def_RandLatEnum_X
import Definitions.Def_RandLatEnum_latticeOf
import Definitions.Def_RandLatEnum_IsHaarLatticeMeasure
import Definitions.Def_RandLatEnum_rhoL
import Definitions.Def_RandLatEnum_dualInSpan

namespace RandLatEnum

open MeasureTheory KannanLattice.Core
open scoped ENNReal

/-- **Eq. (2.10) (Gaussian mass identities)** (Laarhoven, *Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices*, arXiv:2610.15265 (held version, sha256 8fa7a08a…), §2.3, (2.10), p.16). With
`ρ(L) = Σ_{v∈L} e^{−π‖v‖²}`: Poisson summation `ρ(L) = ρ(L*)/det L` for a lattice `L` and its dual
`L*` in its span, and Siegel's mean value `E_{µ_n}[ρ(L)] = 2` for `n ≥ 2` (zero vector included).

**Formalization Note.** The first identity is for every lattice of any rank `d` in any `ℝᵏ` (the
span of a linearly independent `b`, `det L` its covolume in its span), as the paper uses it for
projected lattices. The defining sum is the definition `rhoL` (in `ℝ≥0∞`) and is not a clause.
The expectation is `∫⁻` against any `SL_n(ℝ)`-invariant Borel probability measure on `X_n`. -/
theorem eq_2_10 :
    (∀ (d k : ℕ) (b : Fin d → EuclideanSpace ℝ (Fin k)), LinearIndependent ℝ b →
      rhoL (lattice b : Set (EuclideanSpace ℝ (Fin k))) =
        rhoL (dualInSpan (lattice b)) / ENNReal.ofReal (latticeDet b)) ∧
    (∀ n : ℕ, 2 ≤ n → ∀ μ : Measure (X n), IsHaarLatticeMeasure μ →
      ∫⁻ x, rhoL (latticeOf x : Set (EuclideanSpace ℝ (Fin n))) ∂μ = 2) := by sorry

end RandLatEnum
