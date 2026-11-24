-- Prove2me | Theorems.Thm_SmithRegenerative_Moments_Supplement_corollary_2_1
-- name    : SmithRegenerative.Moments.Supplement.corollary_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T05:47:05.077805+00:00
-- url     : https://prove2.me/theorems/b617f2f2-6745-4138-86ee-34c9b0979859
-- title:
--   Corollary 2·1 — equilibrium with defective first regeneration
-- statement:
--   Let an equilibrium event be aperiodic and satisfy one of the three alternatives in Theorem 2(iv) for $A$. Its first regeneration need not be certain. With $q_z=P_z(t_0<\infty)$,
--   $$\lim_{t\to\infty}\{P_z(x_t\in A)-P_z(x_t\in A,t_0>t)\}=\frac{q_z}{\mu_1}\int_0^\infty\phi_A(v)P(t_1>v)\,dv.$$
--   The limit is zero when $\mu_1=\infty$, a case allowed by the integrable-monotone alternative. The residual term is subtracted, without any hypothesis about its limit. This is the defective-delay equilibrium limit used in Theorem 5.
--
--   Differences from the source:
--   - reading: Printed T_{n_t} is called the last occurrence in (3·4·1). → Use the last epoch at or before t, which is T_{n_t−1} under (2·1·3).; reason: The printed index otherwise gives a future epoch and negative elapsed time. The probability representation itself is preserved.
--   - encoding: Real time and the paper’s distribution-function notation. → Probability measures with explicit mass at infinity and real-time limits; lattice sampling alone uses natural indices.; reason: Preserve defective laws, infinite means and the exact asymptotic domain without total-function defaults.
-- source:
--   Smith, Regenerative stochastic processes, Proc. R. Soc. Lond. A 232(1188):6–31 (1955), DOI 10.1098/rspa.1955.0198, p. 16, Corollary 2·1

import Mathlib
import Definitions.Def_SmithRegenerative_Moments_Supplement_Equilibrium

namespace SmithRegenerative.Moments.Supplement

open MeasureTheory Filter Topology

/-- Smith (1955), Corollary 2·1, p. 16, (3·4·8).
Formalization Note: retain all alternatives of Theorem 2(iv); the finite first-delay
mass may be any number in [0,1]. The no-first-entry term is subtracted without an
assumption that it tends to zero. Infinite cycle mean gives zero. -/
theorem corollary_2_1 {Ω X Z : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (E : Equilibrium Ω X Z) (z : Z) (A : Set X) (hA : A ∈ E.sets)
    (haper : Aperiodic E.F) (hiv : RenewalConditions E A) :
    (extendedMean E.F = ⊤ →
      Tendsto (fun t : ℝ => (E.P z {ω | E.x t ω ∈ A}).toReal -
        (E.P z {ω | E.x t ω ∈ A ∧ ENNReal.ofReal t < E.τ 0 ω}).toReal)
        atTop (𝓝 0)) ∧
    (extendedMean E.F ≠ ⊤ →
      Tendsto (fun t : ℝ => (E.P z {ω | E.x t ω ∈ A}).toReal -
        (E.P z {ω | E.x t ω ∈ A ∧ ENNReal.ofReal t < E.τ 0 ω}).toReal)
        atTop (𝓝 ((E.K z (Set.Iio ⊤)).toReal / (extendedMean E.F).toReal *
          ∫ v in Set.Ioi 0, kernel E A v))) := by sorry

end SmithRegenerative.Moments.Supplement
