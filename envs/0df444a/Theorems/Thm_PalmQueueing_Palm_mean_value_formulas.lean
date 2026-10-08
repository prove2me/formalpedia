-- Prove2me | Theorems.Thm_PalmQueueing_Palm_mean_value_formulas
-- name    : PalmQueueing.Palm.mean_value_formulas
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T20:59:19.940142+00:00
-- url     : https://prove2.me/theorems/5dcf5464-e5cb-4b35-a721-de92c49b002e
-- title:
--   Eqs. (1.3.2)-(1.3.3) — the mean-value formulas
-- statement:
--   Let $(N, \theta_t, P)$ be a stationary point process with finite intensity and $P^0_N$
--   the associated Palm probability. Let $\{Z_t\}$, $t \in \mathbb{R}$, be a stochastic process with
--   values in a measurable space $(K, \mathcal{K})$ such that
--   $$ Z_t = Z_0 \circ \theta_t . \tag{1.3.1} $$
--   Then for all non-negative measurable functions
--   $g : (K, \mathcal{K}) \to (\mathbb{R}, \mathcal{B})$,
--   $$ E\big[g(Z_0)\big] \;=\; \frac{E^0_N\Big[\int_0^{T_1} g(Z_t)\,dt\Big]}{E^0_N[T_1]}
--   \tag{1.3.2} $$
--   and
--   $$ E^0_N\big[g(Z_0)\big] \;=\;
--   \frac{E\Big[\sum_{n \in \mathbb{Z}} g(Z_{T_n}) \mathbf{1}_{\{T_n \in (0,1]\}}\Big]}
--   {E\Big[\sum_{n \in \mathbb{Z}} \mathbf{1}_{\{T_n \in (0,1]\}}\Big]} . \tag{1.3.3} $$
--
--   The book notes that these "just rephrase the inversion formula (1.2.25) and the definition formula
--   (1.2.1) of $P^0_N$", and that (1.3.2) is well known in the theory of renewal and regenerative
--   processes.
--
--   Both denominators are non-zero and finite: $E^0_N[T_1] = 1/\lambda$ by (1.2.27), and the
--   denominator of (1.3.3) is $\lambda$ itself.
-- source:
--   Baccelli & Bremaud, Elements of Queueing Theory: Palm Martingale Calculus and Stochastic Recurrences, 2nd ed., Springer 2003, p. 21, §1.3.1, Eqs. (1.3.2)-(1.3.3)

import Mathlib
import Definitions.Def_PalmQueueing_Palm_PointProcess

/-!
# Eqs. (1.3.2) and (1.3.3): the mean-value formulas (§1.3.1, p.21)
-/

namespace PalmQueueing.Palm

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The mean-value formulas**, Eqs. (1.3.2) and (1.3.3) (§1.3.1, p.21). Let `{Z_t}` take values
in a measurable space `(K, 𝒦)` and satisfy `(1.3.1) Z_t = Z₀ ∘ θ_t`. Then for every non-negative
measurable `g : (K, 𝒦) → (ℝ, B)`, the stationary and Palm expectations of `g(Z₀)` each express the
other as a ratio:

`(1.3.2)  E[g(Z₀)] = E⁰_N[ ∫_0^{T₁} g(Z_t) dt ] / E⁰_N[T₁]`,

`(1.3.3)  E⁰_N[g(Z₀)] = E[ Σ_{n ∈ ℤ} g(Z_{T_n}) 1_{T_n ∈ (0,1]} ] / E[ Σ_{n ∈ ℤ} 1_{T_n ∈ (0,1]} ]`.

The book records that these "just rephrase the inversion formula (1.2.25) and the definition
formula (1.2.1) of `P⁰_N`", and that (1.3.2) is the familiar renewal- and regenerative-process
identity. Both denominators are non-zero and finite: `E⁰_N[T₁] = 1/λ` by (1.2.27) and the second is
`λ` itself. -/
theorem mean_value_formulas {K : Type*} [MeasurableSpace K] (S : PalmSetting Ω)
    (Z : ℝ → Ω → K) (hZmeas : ∀ t, Measurable (Z t))
    (hZ : ∀ (t : ℝ) (ω : Ω), Z t ω = Z 0 (S.θ t ω))
    (g : K → ENNReal) (hg : Measurable g) :
    (∫⁻ ω, g (Z 0 ω) ∂S.P
        = (∫⁻ ω, ∫⁻ t in Set.Ioc (0 : ℝ) (S.N.T 1 ω), g (Z t ω) ∂(volume : Measure ℝ) ∂S.P0)
            / (∫⁻ ω, ENNReal.ofReal (S.N.T 1 ω) ∂S.P0))
      ∧ (∫⁻ ω, g (Z 0 ω) ∂S.P0
        = (∫⁻ ω, ∑' n : ℤ,
              Set.indicator (Set.Ioc (0 : ℝ) 1) (fun _ => g (Z (S.N.T n ω) ω)) (S.N.T n ω) ∂S.P)
            / (∫⁻ ω, ∑' n : ℤ,
              Set.indicator (Set.Ioc (0 : ℝ) 1) (fun _ => (1 : ENNReal)) (S.N.T n ω) ∂S.P)) := by sorry

end PalmQueueing.Palm
