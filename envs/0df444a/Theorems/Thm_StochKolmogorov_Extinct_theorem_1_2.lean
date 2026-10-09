-- Prove2me | Theorems.Thm_StochKolmogorov_Extinct_theorem_1_2
-- name    : StochKolmogorov.Extinct.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:33:02.838176+00:00
-- url     : https://prove2.me/theorems/43e412d4-4d71-4ffd-a615-9ed5cd31aaaa
-- title:
--   Theorem 1.2 — extinction in a small positive moment
-- statement:
--   Suppose the Kolmogorov system satisfies Assumption 1.1 and some boundary ergodic invariant law $\mu$ satisfies Assumption 1.3. For every $\delta_0\in(0,\min\{\gamma_b/2,1\})$ satisfying (3.2), every $\delta\in(0,\delta_0)$, and every strictly positive initial state $x$,
--
--   $$\lim_{t\to\infty}\mathbb E_x\left(\min_{1\le i\le n}X_i(t)\right)^\delta=0.$$
--
--   The paper proves this in Theorem 5.1; it implies Theorem 1.2's assertion that all sufficiently small positive moments vanish in the limit. It does not by itself identify which particular species disappears.
--
--   **Formalization Note** Theorem 5.1 prints $\delta<\delta_0$ without $\delta>0$; the latter is explicit in Theorem 1.2 and necessary at $\delta=0$. The formulation is uniform over every admissible choice of $\delta_0$. Coordinates are zero-based `Fin n` in Lean; $n\ge1$ excludes an empty minimum.
--
--   **Moderation note** The finite moment at each time is stated explicitly alongside the limit, preventing a nonintegrable Bochner integral from taking Lean’s default value.
-- source:
--   Hening, Nguyen, Coexistence and extinction for stochastic Kolmogorov systems, arXiv:1704.06984v1, Theorem 1.2, p. 7, (1.10); Theorem 5.1, p. 22, (5.5)

import Mathlib
import Definitions.Def_StochKolmogorov_Extinct_Extinction

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace StochKolmogorov.Extinct

open EthierKurtz

theorem theorem_1_2 {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (hX : IsSolutionFamily P C B X)
    (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (mu : Measure (SDEState n)) (h13 : Assumption13 P C X mu)
    (δ₀ : ℝ) (hδ₀ : IsDelta0 C γb δ₀) :
    ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ x ∈ openOrthant n,
      (∀ t : ℝ≥0, Integrable (fun ω => (⨅ i : Fin n, X x t ω i) ^ δ) P) ∧
        Tendsto (fun t : ℝ≥0 => ∫ ω, (⨅ i : Fin n, X x t ω i) ^ δ ∂P)
          atTop (𝓝 0) := by sorry

end StochKolmogorov.Extinct
