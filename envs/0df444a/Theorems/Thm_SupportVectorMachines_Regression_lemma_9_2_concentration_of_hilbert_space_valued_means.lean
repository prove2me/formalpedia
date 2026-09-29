-- Prove2me | Theorems.Thm_SupportVectorMachines_Regression_lemma_9_2_concentration_of_hilbert_space_valued_means
-- name    : SupportVectorMachines.Regression.lemma_9_2_concentration_of_hilbert_space_valued_means
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-19T23:15:17.278545+00:00
-- url     : https://prove2.me/theorems/4779a7b8-f1fc-43a5-808f-648da290308d
-- title:
--   Lemma 9.2 — concentration of Hilbert-space-valued sample means
-- statement:
--   This is Lemma 9.2 of Steinwart & Christmann, *Support Vector Machines* (Springer 2008,
--   p. 336), this mission's goal: the concentration inequality the book uses "to bound the
--   probability of $|R_{L,P}(f_{D,\lambda}) - R_{L,P}(f_{P,\lambda})| \le \varepsilon$ for
--   $|D| \to \infty$" inside the proof of Theorem 9.1, the chapter's main SVM-regression
--   consistency theorem.
--
--   Let $Z$ be a measurable space, $P$ a distribution on $Z$, $H$ a separable Hilbert space, and
--   $g : Z \to H$ measurable with $\|g\|_q := (\mathbb E_P\|g\|_H^q)^{1/q} < \infty$ for some
--   $q \in (1,\infty)$. Write $q^* := \min\{1/2, 1/q'\}$ where $1/q + 1/q' = 1$ (equivalently
--   $q^* = \min\{1/2,\, 1-1/q\}$). Then there is a universal constant $c_q > 0$ such that, for
--   every $\varepsilon > 0$ and $n \ge 1$,
--   $$
--   P^n\!\left(\left\{(z_1,\dots,z_n) \in Z^n :
--     \left\|\frac1n\sum_{i=1}^n g(z_i) - \mathbb E_P g\right\|_H \ge \varepsilon\right\}\right)
--   \le c_q\left(\frac{\|g\|_q}{\varepsilon\, n^{q^*}}\right)^{q}.
--   $$
--
--   The lemma is a genuine generalization of the classical Chebyshev/Bernstein-type tail bound to
--   Hilbert-space-valued sample means, phrased purely in terms of a single moment condition (no
--   exponential-moment/sub-Gaussian assumption); its proof combines Markov's inequality with the
--   two milestones of this mission (the symmetrization inequality, Theorem A.8.1, and Kahane's
--   inequality, Theorem A.8.3) and an explicit second-moment computation for Rademacher sums
--   (the book's Eq. (9.4), an unnumbered consequence of the two theorems, not separately
--   formalized here per Hard Rule 5).
--
--   **Formalization Note** $P^n$ (the book's $n$-fold product distribution on $Z^n$) is
--   `MeasureTheory.Measure.pi (fun _ : Fin n => P) : Measure (Fin n → Z)`, and $Z^n$ is
--   `Fin n → Z`. The quantifier for the universal constant is `∃ c, 0 < c ∧ ∀ ε, 0 < ε → ∀ n, 1 ≤
--   n → …`, with `∃ c` placed before both `∀ ε` and `∀ n`, matching the book's "there exists a
--   universal constant $c_q$... such that, for all $\varepsilon>0$ and all $n\ge1$" exactly
--   (Trap 8 guard: $c_q$ depends only on $q$, never on $\varepsilon$ or $n$). $q^*$ is substituted
--   directly as `min (1/2) (1 - 1/q)` rather than introduced via a separate `q'` variable, since
--   `1/q + 1/q' = 1` pins down `q' = q/(q-1)` uniquely and `1/q' = 1 - 1/q` follows immediately —
--   an algebraic simplification, not a change of content.
-- source:
--   Steinwart & Christmann, Support Vector Machines, Springer 2008, p. 336, Lemma 9.2

import Mathlib

open MeasureTheory TopologicalSpace

namespace SupportVectorMachines.Regression

/-- Lemma 9.2, p. 336: let `Z` be a measurable space, `P` a distribution on `Z`, `H` a separable
Hilbert space, and `g : Z → H` measurable with `‖g‖_q := (E_P‖g‖^q_H)^{1/q} < ∞` for some
`q ∈ (1,∞)`. Write `q* := min{1/2, 1/q'}` where `1/q + 1/q' = 1`, i.e. `q* = min{1/2, 1 - 1/q}`.
Then there is a universal constant `c_q > 0` such that, for all `ε > 0` and `n ≥ 1`,
`P^n{(z₁,…,zₙ) : ‖(1/n)∑ᵢg(zᵢ) - E_Pg‖_H ≥ ε} ≤ c_q (‖g‖_q / (ε n^{q*}))^q`. -/
theorem lemma_9_2_concentration_of_hilbert_space_valued_means
    {Z : Type*} [MeasurableSpace Z] (P : Measure Z) [IsProbabilityMeasure P]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SeparableSpace H]
    (g : Z → H) (hg : Measurable g)
    (q : ℝ) (hq : 1 < q) (hgInt : Integrable (fun z => ‖g z‖ ^ q) P) :
    ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ∀ n : ℕ, 1 ≤ n →
      (Measure.pi (fun _ : Fin n => P))
          {z : Fin n → Z | ε ≤ ‖(n : ℝ)⁻¹ • (∑ i, g (z i)) - ∫ z', g z' ∂P‖} ≤
        ENNReal.ofReal
          (c * ((∫ z, ‖g z‖ ^ q ∂P) ^ (1 / q) /
              (ε * (n : ℝ) ^ (min (1 / 2 : ℝ) (1 - 1 / q)))) ^ q) := by sorry

end SupportVectorMachines.Regression
