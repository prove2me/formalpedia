-- Prove2me | Theorems.Thm_StochKolmogorov_Extinct_lemma_3_1
-- name    : StochKolmogorov.Extinct.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:33:24.467903+00:00
-- url     : https://prove2.me/theorems/4f3793d0-0fce-47b2-a6e8-50aba1db712b
-- title:
--   Lemma 3.1 — strong solution, invariant faces and moment bound
-- statement:
--   Under Assumption 1.1, the strong solution of the Kolmogorov equation is pathwise unique, and a solution beginning in a face with precisely the species $I$ present remains there almost surely for all time. For positive weights $p$ with $\|p\|_1\le\delta_0$, write $V(x)=(1+c^\top x)/\prod_i x_i^{p_i}$. For every interior start $x$ and $t\ge0$,
--
--   $$\mathbb E_x[V(X(t))^{\delta_0}]\le e^{\delta_0 Ht}V(x)^{\delta_0}.$$
--
--   This supplies the pathwise domain and moment control used in the extinction argument.
--
--   **Formalization Note** A family of strong solutions is fixed in the standing setting; uniqueness compares any other strong solution driven by the same Brownian motion with this family. The face statement is almost sure at every time on one common full-measure event.
--
--   **Moderation note** The expected moment includes its integrability, so a nonintegrable real integral cannot satisfy the estimate through Lean’s default value.
-- source:
--   Hening, Nguyen, Coexistence and extinction for stochastic Kolmogorov systems, arXiv:1704.06984v1, Lemma 3.1, p. 14

import Mathlib
import Definitions.Def_StochKolmogorov_Extinct_Extinction

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace StochKolmogorov.Extinct

open EthierKurtz

theorem lemma_3_1 {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (hX : IsSolutionFamily P C B X)
    (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (δ₀ : ℝ) (hδ₀ : IsDelta0 C γb δ₀) :
    (∀ x ∈ orthant n, ∀ Y : ℝ≥0 → Ω → SDEState n,
      SolvesBrownianSDE P (diffusion C) (drift C) B (fun _ => x) Y →
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0, Y t ω = X x t ω) ∧
    (∀ (I : Finset (Fin n)) (x : SDEState n), x ∈ orthant n →
      (∀ i, i ∈ I ↔ 0 < x i) →
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        (∀ i ∈ I, 0 < X x t ω i) ∧ (∀ i, i ∉ I → X x t ω i = 0)) ∧
    (∀ (p : SDEState n), p ∈ openOrthant n → l1 p ≤ δ₀ →
      ∀ x ∈ openOrthant n, ∀ t : ℝ≥0,
        Integrable (fun ω => (Vfun c p (X x t ω)) ^ δ₀) P ∧
        ∫ ω, (Vfun c p (X x t ω)) ^ δ₀ ∂P ≤
          Real.exp (δ₀ * Hconst C c γb δ₀ * (t : ℝ)) * (Vfun c p x) ^ δ₀) := by sorry

end StochKolmogorov.Extinct
