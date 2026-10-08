-- Prove2me | Theorems.Thm_PalmQueueing_Palm_neveu_exchange_formula
-- name    : PalmQueueing.Palm.neveu_exchange_formula
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T21:05:24.075875+00:00
-- url     : https://prove2.me/theorems/a98e0e25-df2b-4773-8528-30cef94126a7
-- title:
--   Eq. (1.3.4) — the Neveu exchange formula
-- statement:
--   **The Neveu exchange formula.** Let $(N, \theta_t, P)$ and $(N', \theta_t, P)$ be two
--   stationary point processes with finite intensities $\lambda$ and $\lambda'$ respectively. They are
--   *jointly* stationary, in the sense that their stationarity is relative to the same quadruple
--   $(\Omega, \mathcal{F}, P, \theta_t)$. Then
--   $$ \lambda E^0_N[f] \;=\; \lambda' E^0_{N'}\Big[ \int_{(0, T'_1]} (f \circ \theta_t)\, N(dt) \Big]
--   \tag{1.3.4} $$
--   for all non-negative measurable functions $f : (\Omega, \mathcal{F}) \to (\mathbb{R}, \mathcal{B})$,
--   where $T'_n$ is the $n$-th point of $N'$.
--
--   The formula exchanges the roles of the two processes: it converts an $N$-Palm expectation into an
--   $N'$-Palm expectation of a sum over the points of $N$ falling in one $N'$-cycle. Taking
--   $N' = N$ recovers the trivial identity; taking $f = 1$ gives
--   $\lambda = \lambda' E^0_{N'}[N((0,T'_1])]$, the intensity ratio.
--
--   The two hypotheses that the flows and the stationary probabilities of the two settings agree are
--   what "jointly stationary, relative to the same quadruple" means.
-- source:
--   Baccelli & Bremaud, Elements of Queueing Theory: Palm Martingale Calculus and Stochastic Recurrences, 2nd ed., Springer 2003, p. 21, §1.3.2, Eq. (1.3.4)

import Mathlib
import Definitions.Def_PalmQueueing_Palm_PointProcess

/-!
# Eq. (1.3.4): the Neveu exchange formula (§1.3.2, p.21)
-/

namespace PalmQueueing.Palm

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The Neveu exchange formula**, Eq. (1.3.4) (§1.3.2, p.21). Let `(N, θ_t, P)` and
`(N', θ_t, P)` be two stationary point processes with finite intensities `λ` and `λ'`, *jointly*
stationary in the sense that their stationarity is relative to the same quadruple
`(Ω, F, P, θ_t)`. Then

`λ E⁰_N[f] = λ' E⁰_{N'} [ ∫_{(0, T'₁]} (f ∘ θ_t) N(dt) ]`

for all non-negative measurable `f : (Ω, F) → (ℝ, B)`, where `T'_n` is the `n`-th point of `N'`.

The formula exchanges the roles of the two processes: it expresses an `N`-Palm expectation as an
`N'`-Palm expectation of a sum over the points of `N` in one `N'`-cycle. Its two hypotheses `hflow`
and `hprob` are what "jointly stationary" means here. -/
theorem neveu_exchange_formula (S S' : PalmSetting Ω)
    (hflow : S'.θ = S.θ) (hprob : S'.P = S.P)
    (f : Ω → ENNReal) (hf : Measurable f) :
    ENNReal.ofReal S.lam * ∫⁻ ω, f ω ∂S.P0
      = ENNReal.ofReal S'.lam *
          ∫⁻ ω, ∫⁻ t in Set.Ioc (0 : ℝ) (S'.N.T 1 ω), f (S.θ t ω) ∂(S.N.count ω) ∂S'.P0 := by sorry

end PalmQueueing.Palm
