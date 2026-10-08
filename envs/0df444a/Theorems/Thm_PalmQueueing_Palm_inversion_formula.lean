-- Prove2me | Theorems.Thm_PalmQueueing_Palm_inversion_formula
-- name    : PalmQueueing.Palm.inversion_formula
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T20:55:40.617495+00:00
-- url     : https://prove2.me/theorems/5476f03f-89e1-4b59-ba38-cfee5cf67d6e
-- title:
--   Eq. (1.2.25) — the inversion formula of Ryll-Nardzewski and Slivnyak
-- statement:
--   **The inversion formula of Ryll-Nardzewski and Slivnyak.** The original
--   ($\theta_t$-invariant) probability can be recovered from the Palm probability by averaging over one
--   inter-point interval: for all non-negative random variables $f$,
--   $$ E[f] \;=\; \lambda\, E^0_N \Big[ \int_0^{T_1} (f \circ \theta_t)\, dt \Big] . \tag{1.2.25} $$
--
--   The book derives it from Mecke's formula applied to
--   $v(\omega, t) = h(\theta_{-t}\omega, t) f(\theta_{-t}\omega)$ for any $h$ with
--   $\int_{\mathbb{R}} h(\omega, t) N(\omega, dt) = 1$ $P$-a.s. (1.2.23), specialized to
--   $h(\omega, t) = \mathbf{1}_{[T_0(\omega), 0)}(t)$ and using that $-T_0 \circ \theta_u = u$
--   $P^0_N$-a.s. for all $u \in [0, T_1)$.
--
--   Two specializations appear on the same page: $f = \mathbf{1}_A$ gives
--   $P(A) = \lambda \int_0^\infty P^0_N(T_1 > t,\ \theta_t \in A)\, dt$ (1.2.26), and $f = 1$ gives
--   $$ \lambda E^0_N[T_1] = 1 . \tag{1.2.27} $$
--
--   It is stated for **all** non-negative random variables, not only bounded ones; restricting it to
--   bounded $f$ would be a strictly weaker statement than the book's.
-- source:
--   Baccelli & Bremaud, Elements of Queueing Theory: Palm Martingale Calculus and Stochastic Recurrences, 2nd ed., Springer 2003, p. 20, Eq. (1.2.25)

import Mathlib
import Definitions.Def_PalmQueueing_Palm_PointProcess

/-!
# Eq. (1.2.25): the inversion formula of Ryll-Nardzewski and Slivnyak (p.20)
-/

namespace PalmQueueing.Palm

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The inversion formula of Ryll-Nardzewski and Slivnyak**, Eq. (1.2.25) (p.20): the
`θ_t`-invariant probability is recovered from the Palm probability by averaging over one inter-point
interval,

`E[f] = λ E⁰_N [ ∫_0^{T₁} (f ∘ θ_t) dt ]`,

for **all** non-negative random variables `f` — not only bounded ones. Taking `f = 1` gives
`λ E⁰_N[T₁] = 1` (1.2.27), and `f = 1_A` gives
`P(A) = λ ∫_0^∞ P⁰_N(T₁ > t, θ_t ∈ A) dt` (1.2.26). -/
theorem inversion_formula (S : PalmSetting Ω) (f : Ω → ENNReal) (hf : Measurable f) :
    ∫⁻ ω, f ω ∂S.P
      = ENNReal.ofReal S.lam *
          ∫⁻ ω, ∫⁻ t in Set.Ioc (0 : ℝ) (S.N.T 1 ω), f (S.θ t ω) ∂(volume : Measure ℝ) ∂S.P0 := by sorry

end PalmQueueing.Palm
