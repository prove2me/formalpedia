-- Prove2me | Theorems.Thm_PalmQueueing_Recurrence_stability_region
-- name    : PalmQueueing.Recurrence.stability_region
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T00:49:02.960674+00:00
-- url     : https://prove2.me/theorems/cf1f62fd-6b46-4087-9747-c6025ac9a805
-- title:
--   Theorem 2.11.3 — the stability region and the saturation rule
-- statement:
--   **Theorem 2.11.3**, which the book introduces as "the main result on the stability
--   region":
--
--   If $\lim Z_{[-n,0]} \to \infty$ a.s., then $\lambda\gamma(0) \ge 1$. If $\lambda\gamma(0) > 1$,
--   then $\lim Z_{[-n,0]} \to \infty$ a.s.
--
--   This is the **saturation rule**, proved. The rule says: saturate the queues which are fed by the
--   external arrival stream with an infinite customer population; if $\mu$ denotes the intensity of
--   the departure stream in this saturated system, then the system is stable when the intensity
--   $\lambda$ of the arrival process satisfies $\lambda < \mu$. In the Monotone–Homogeneous–Separable
--   framework $\gamma(0)$ is exactly the growth rate of the saturated system — taking $c = 0$ puts
--   every arrival at the origin — so $\mu = \gamma(0)^{-1}$ and the criterion reads
--   $\lambda\gamma(0) < 1$. The book is careful that the rule "does not hold for all systems"; §2.11's
--   aim is to prove it for Monotone–Homogeneous–Separable networks under standard stationary ergodic
--   assumptions.
--
--   **Two implications, and the gap between them is deliberate.** Instability forces
--   $\lambda\gamma(0) \ge 1$; $\lambda\gamma(0) > 1$ forces instability. The boundary case
--   $\lambda\gamma(0) = 1$ is left undecided, exactly as the critical case $\rho = 1$ of Loynes'
--   theorem is. Stating a single equivalence would close a gap the book does not close.
--
--   The second assertion is proved first, by comparing $N$ with the saturated process $Q$ whose points
--   are all $0$: the sub-additive and monotonicity properties give
--   $Z_{[-n,0]}(N) \ge Z_{[-n,0]}(Q) + T_{-n} - T_0$, so
--   $\liminf_n Z_{[-n,0]}(N)/n \ge \gamma(0) - \lambda^{-1} > 0$. The first uses the random indices
--   $K_l = \min\{n \ge 1 : Z_{[-n,0]}(N) \ge T_l - T_0\}$, $P^0$-a.s. finite when $Z_{[-n,0]}$ tends
--   to infinity.
--
--   **Formalization Note.** The standing assumptions of §2.11.4 are binders: the marked point process
--   $N = \{(T_n, \xi_n)\}$ is read on its Palm space $(\Omega, \mathcal{F}, P^0, \theta)$, so
--   $T_0 = 0$, $T_n \circ \theta = T_{n+1} - T_1$, $\xi_n \circ \theta = \xi_{n+1}$ and
--   $(P^0, \theta)$ is ergodic; $T_n \le T_{n+1}$; $E^0\tau_n = \lambda^{-1}$ with $\lambda > 0$;
--   $E^0 Z_n < \infty$; $X$ is measurable and in the Monotone–Homogeneous–Separable framework,
--   including (2.11.16); $\gamma(0)$ is the a.s. limit of Property 2.11.9 at $c = 0$. The marks are
--   part of the model: without them $Z_n$ would be a deterministic constant and the theorem would
--   only cover networks with deterministic service.
-- source:
--   Baccelli & Bremaud, Elements of Queueing Theory: Palm Martingale Calculus and Stochastic Recurrences, 2nd ed., Springer 2003, p. 166, Theorem 2.11.3

import Mathlib
import Definitions.Def_PalmQueueing_Recurrence_Saturation

/-!
# Theorem 2.11.3: the stability region and the saturation rule (§2.11.4, p.166)
-/

namespace PalmQueueing.Recurrence

open MeasureTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Theorem 2.11.3** (p.166), which the book introduces as "the main result on the stability
region":

If `lim Z_{[-n,0]} → ∞` a.s., then `λ γ(0) ≥ 1`. If `λ γ(0) > 1`, then `lim Z_{[-n,0]} → ∞` a.s.

This is the **saturation rule** proved. The rule says: saturate the queues fed by the external
arrival stream, measure the departure intensity `µ` of the saturated system, and declare the
system stable when `λ < µ`. In the Monotone-Homogeneous-Separable framework, `γ(0)` is exactly the
growth rate of the *saturated* system — `c = 0` puts every arrival at the origin — so `µ = γ(0)⁻¹`
and the criterion reads `λ γ(0) < 1`. The book notes that the rule "does not hold for all systems";
the aim of §2.11 is to prove it for this class under standard stationary ergodic assumptions.

**Two implications, and the gap between them is deliberate.** Instability forces `λγ(0) ≥ 1`;
`λγ(0) > 1` forces instability. The boundary case `λγ(0) = 1` is not decided, exactly as the
critical case of Loynes' theorem is not, and closing the gap by stating a single equivalence would
assert something the book does not prove.

The hypotheses are §2.11.4's (p.165): the marked point process `N` is stationary and ergodic and
its Palm space `(Ω, F, P⁰, θ)` is the reference probability space. Concretely, `θ` is the shift to
the next point, so that `T_0 = 0`, `T_n ∘ θ = T_{n+1} − T_1` and `ξ_n ∘ θ = ξ_{n+1}`, and
`(P⁰, θ)` is ergodic; the points are non-decreasing (p.161); `E⁰τ_n = λ^{-1} < ∞` and
`E⁰Z_n < ∞` with `Z_n = Z_{[n,n]}`; `X` is in the Monotone-Homogeneous-Separable framework and is
measurable; and `γ(0)` is the growth rate supplied by Property 2.11.9 at `c = 0`. -/
theorem stability_region {E : Type*} [MeasurableSpace E]
    (P0 : Measure Ω) [IsProbabilityMeasure P0] (θ : Ω ≃ᵐ Ω)
    (herg : Ergodic θ P0)
    (X : (ℤ → ℝ) → (ℤ → E) → ℤ → ℤ → ℝ) (hX : IsMHS X)
    (hXmeas : ∀ m n : ℤ, Measurable (fun p : (ℤ → ℝ) × (ℤ → E) => X p.1 p.2 m n))
    (T : Ω → ℤ → ℝ) (ξ : Ω → ℤ → E)
    (hTmeas : ∀ n : ℤ, Measurable (fun ω => T ω n))
    (hξmeas : ∀ n : ℤ, Measurable (fun ω => ξ ω n))
    (hT : ∀ ω : Ω, Monotone (T ω))
    (hT0 : ∀ ω : Ω, T ω 0 = 0)
    (hTθ : ∀ (ω : Ω) (n : ℤ), T (θ ω) n = T ω (n + 1) - T ω 1)
    (hξθ : ∀ (ω : Ω) (n : ℤ), ξ (θ ω) n = ξ ω (n + 1))
    (lam : ℝ) (hlam : 0 < lam)
    (hlam_def : ∀ n : ℤ, ∫ ω, (T ω (n + 1) - T ω n) ∂P0 = lam⁻¹)
    (hZint : ∀ n : ℤ, Integrable (fun ω => mhsZ X (T ω) (ξ ω) n n) P0)
    (gam0 : ℝ) (hgam0 : IsGrowthRate P0 X T ξ 0 gam0) :
    ((∀ᵐ ω ∂P0, Tendsto (fun n : ℕ => mhsZ X (T ω) (ξ ω) (-(n : ℤ)) 0) atTop atTop) →
      1 ≤ lam * gam0) ∧
    (1 < lam * gam0 →
      ∀ᵐ ω ∂P0, Tendsto (fun n : ℕ => mhsZ X (T ω) (ξ ω) (-(n : ℤ)) 0) atTop atTop) := by sorry

end PalmQueueing.Recurrence
