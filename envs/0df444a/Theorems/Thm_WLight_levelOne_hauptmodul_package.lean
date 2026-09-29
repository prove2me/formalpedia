-- Prove2me | Theorems.Thm_WLight_levelOne_hauptmodul_package
-- name    : WLight.levelOne_hauptmodul_package
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/3bfac678-351d-51fb-81b3-f37cf843690b
-- title:
--   Level-one hauptmodul package: polynomials in j, surjectivity, q-expansion principle
-- statement:
--   A conjunction of five assertions about the level-one functions $E_4$, $\Delta$ and $j=E_4^3/\Delta$ on $\mathbb{H}$. (a) For every $m\in\mathbb{N}$ and every $h:\mathbb{H}\to\mathbb{C}$ that is differentiable as a map of complex manifolds, satisfies $h\mid[0]\gamma=h$ for all $\gamma\in\mathrm{SL}(2,\mathbb{Z})$ under the weight-$0$ slash action, and is such that $h\cdot\Delta^m$ is bounded at $i\infty$, there is $P\in\mathbb{C}[X]$ with $\deg P\le m$ and $h(\tau)=P\bigl(E_4(\tau)^3/\Delta(\tau)\bigr)$ for all $\tau$. (b) The same with an intermediate field $k$ of $\mathbb{C}/\mathbb{Q}$ and a width $N\neq 0$: if moreover $(h\cdot\Delta^m)\circ\mathtt{ofComplex}$ is periodic with period $N$ and every coefficient of the width-$N$ $q$-expansion of $h\cdot\Delta^m$ lies in $k$, then $P$ may be taken with $\deg P\le m$, all coefficients in $k$, and $h=P(E_4^3/\Delta)$. (c) The map $\tau\mapsto E_4(\tau)^3/\Delta(\tau)$ is surjective. (d) For $m\in\mathbb{N}$ and $P\in\mathbb{C}[X]$ with $\deg P\le m$: if every coefficient of the power series $\sum_{i=0}^{m}C(P_i)\,q_1(E_4)^{3i}\,q_1(\Delta)^{m-i}$, formed from the width-$1$ $q$-expansions of $E_4$ and $\Delta$, is rational, then every $P_i$ is rational. (e) The same implication with "rational" replaced throughout by "lying in a given intermediate field $k$ of $\mathbb{C}/\mathbb{Q}$".
--
--   These are the level-one inputs to the $q$-expansion-principle argument: parts (a) and (b) identify $\mathrm{SL}(2,\mathbb{Z})$-invariant holomorphic functions with at most polar growth at the cusp as polynomials in the modular invariant $j$, with coefficients controlled by the $q$-expansion, part (c) allows such polynomial identities to be tested by evaluation, and parts (d), (e) transfer rationality information from a single combined $q$-series to the polynomial coefficients. The package is cited in the level-$N$ function-field results, among them [`WLight.exists_levelFraction_of_stable_family`](thm.html#WLight.exists_levelFraction_of_stable_family), [`WLight.exists_monicRel_j_of_mdifferentiable_levelFraction`](thm.html#WLight.exists_monicRel_j_of_mdifferentiable_levelFraction) and [`WLight.frickeFunction_orbit_package`](thm.html#WLight.frickeFunction_orbit_package).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WLight_levelOne_hauptmodul_package.lean

import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Geometry.Manifold.Notation
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Complex Real Polynomial
open UpperHalfPlane
open scoped Manifold MatrixGroups ModularForm

theorem WLight.levelOne_hauptmodul_package :

    (∀ (m : ℕ) (h : ℍ → ℂ), MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h →
      (∀ γ : SL(2, ℤ), h ∣[(0 : ℤ)] γ = h) →
      IsBoundedAtImInfty (h * ModularForm.discriminant ^ m) →
      ∃ P : Polynomial ℂ, P.natDegree ≤ m ∧
        h = fun τ => Polynomial.eval (ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ) P) ∧

    (∀ (k : IntermediateField ℚ ℂ) (N : ℕ), N ≠ 0 → ∀ (m : ℕ) (h : ℍ → ℂ),
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h →
      (∀ γ : SL(2, ℤ), h ∣[(0 : ℤ)] γ = h) →
      Function.Periodic ((h * ModularForm.discriminant ^ m) ∘ ofComplex) N →
      IsBoundedAtImInfty (h * ModularForm.discriminant ^ m) →
      (∀ n : ℕ, (qExpansion N (h * ModularForm.discriminant ^ m)).coeff n ∈ k) →
      ∃ P : Polynomial ℂ, P.natDegree ≤ m ∧ (∀ i, P.coeff i ∈ k) ∧
        h = fun τ => Polynomial.eval (ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ) P) ∧

    Function.Surjective (fun τ : ℍ => ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ) ∧

    (∀ (m : ℕ) (P : Polynomial ℂ), P.natDegree ≤ m →
      (∀ n : ℕ, ∃ q : ℚ, (∑ i ∈ Finset.range (m + 1),
          PowerSeries.C (P.coeff i) * qExpansion 1 ⇑ModularForm.E₄ ^ (3 * i) *
            qExpansion 1 ModularForm.discriminant ^ (m - i)).coeff n = (q : ℂ)) →
      ∀ i : ℕ, ∃ q : ℚ, P.coeff i = (q : ℂ)) ∧

    (∀ (k : IntermediateField ℚ ℂ) (m : ℕ) (P : Polynomial ℂ), P.natDegree ≤ m →
      (∀ n : ℕ, (∑ i ∈ Finset.range (m + 1),
          PowerSeries.C (P.coeff i) * qExpansion 1 ⇑ModularForm.E₄ ^ (3 * i) *
            qExpansion 1 ModularForm.discriminant ^ (m - i)).coeff n ∈ k) →
      ∀ i : ℕ, P.coeff i ∈ k) := by sorry
