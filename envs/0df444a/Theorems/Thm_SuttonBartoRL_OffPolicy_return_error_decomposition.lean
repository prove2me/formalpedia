-- Prove2me | Theorems.Thm_SuttonBartoRL_OffPolicy_return_error_decomposition
-- name    : SuttonBartoRL.OffPolicy.return_error_decomposition
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T16:40:12.591978+00:00
-- url     : https://prove2.me/theorems/7163839c-6cec-4a8e-adce-39a65bca5a4f
-- title:
--   (11.24) / Exercise 11.4 — RE = VE + E[(G_t − v_π(S_t))²]
-- statement:
--   Let $S_t\sim\mu$ on a finite state set $\mathcal S$ and, given $S_t = s$, let the return $G_t$ have distribution $\nu_s$ on $\mathbb R$, with finite second moment and mean $v_\pi(s) = \mathbb E[G_t\mid S_t = s]$ (the on-policy case). Then for every approximate value function $\hat v(\cdot,\mathbf w)$,
--   $$
--   \mathrm{RE}(\mathbf w) = \mathbb E\bigl[(G_t - \hat v(S_t,\mathbf w))^2\bigr] = \mathrm{VE}(\mathbf w) + \mathbb E\bigl[(G_t - v_\pi(S_t))^2\bigr].
--   $$
--
--   The second term does not depend on $\mathbf w$, so RE and VE have the same minimizing parameters: the VE is not learnable from data, but its minimizer is.
--
--   **Formalization Note** The return enters only through its conditional distributions $\nu_s$ (probability measures with finite second moment and mean $v_\pi(s)$); the process generating $G_t$ is not modelled. The parameter space is an arbitrary type, since (11.24) holds for any approximator. The book proves nothing here; it is set as Exercise 11.4.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Eq. (11.24) and Exercise 11.4, p. 275

import Mathlib
import Definitions.Def_SuttonBartoRL_OffPolicy_ReturnError

open MeasureTheory

namespace SuttonBartoRL.OffPolicy

/-- Sutton & Barto (2018), (11.24) and Exercise 11.4, p. 275 (on-policy case). Let `S_t ∼ µ` on a
finite state set and, given `S_t = s`, let the return `G_t` have a distribution `ν_s` on `ℝ` with
finite second moment and mean `v_π(s) = E[G_t | S_t = s]`. Then for every approximate value
function `v̂(·, w)`,
`RE(w) = E[(G_t − v̂(S_t, w))²] = VE(w) + E[(G_t − v_π(S_t))²]`. -/
theorem return_error_decomposition {S W : Type} [Fintype S]
    (μ : S → ℝ) (hμ0 : ∀ s, 0 ≤ μ s) (hμ1 : ∑ s, μ s = 1)
    (ν : S → Measure ℝ) (hprob : ∀ s, IsProbabilityMeasure (ν s))
    (hL2 : ∀ s, MemLp id 2 (ν s))
    (vπ : S → ℝ) (hmean : ∀ s, ∫ g, g ∂(ν s) = vπ s)
    (vhat : W → S → ℝ) (w : W) :
    RE μ ν (vhat w) = VE μ vπ (vhat w) + RE μ ν vπ := by sorry

end SuttonBartoRL.OffPolicy
