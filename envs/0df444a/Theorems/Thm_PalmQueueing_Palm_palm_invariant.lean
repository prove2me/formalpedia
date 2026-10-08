-- Prove2me | Theorems.Thm_PalmQueueing_Palm_palm_invariant
-- name    : PalmQueueing.Palm.palm_invariant
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T20:48:56.912953+00:00
-- url     : https://prove2.me/theorems/08dd160d-ae18-49b8-b240-2055248c9e48
-- title:
--   Eq. (1.2.16) — the Palm probability is invariant under the point shift
-- statement:
--   $P^0_N$ is $\theta$-invariant, where $\theta$ is the **point shift**
--   $\omega \mapsto \theta_{T_1(\omega)}\omega$ — the discrete shift that moves the origin to the next
--   point of the process, not the continuous flow $\{\theta_t\}$ (it is $P$ that is invariant under
--   that).
--
--   $$ P^0_N(A) \;=\; P^0_N(\theta^{-1}(A)) \qquad \text{for all } A \in \mathcal{F} .
--   \tag{1.2.16} $$
--
--   The book's proof applies the defining formula (1.2.1) with $C = (0,t]$ to get
--   $|P^0_N(A) - P^0_N(\theta^{-1}(A))| \le 1/(\lambda t)$ for every $t$, using
--   $\mathbf{1}_{\theta^{-1}(A)} \circ \theta_{T_n} = \mathbf{1}_A \circ \theta_{T_{n+1}}$, and then
--   lets $t \to \infty$.
--
--   Its consequence is the one the rest of the book uses: if $\{Z(t)\}$ is compatible with the flow
--   $\{\theta_t\}$ — equivalently, if it is time-stationary under $P$ — then the sequence
--   $\{Z(T_n)\}$ is a **stationary sequence** under $P^0_N$.
-- source:
--   Baccelli & Bremaud, Elements of Queueing Theory: Palm Martingale Calculus and Stochastic Recurrences, 2nd ed., Springer 2003, p. 17, Eq. (1.2.16)

import Mathlib
import Definitions.Def_PalmQueueing_Palm_PointProcess

/-!
# Eq. (1.2.16): the Palm probability is invariant under the point shift (p.17)
-/

namespace PalmQueueing.Palm

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Eq. (1.2.16)** (p.17). `P⁰_N` is `θ`-invariant, where `θ` is the **point shift**
`ω ↦ θ_{T₁(ω)} ω` — the discrete shift that moves the origin to the next point, not the
continuous flow `{θ_t}` (`P` is what is invariant under that).

This is what makes `{Z(T_n)}` a stationary sequence under `P⁰_N` whenever `{Z(t)}` is compatible
with the flow, which is the form in which the rest of the book uses it. -/
theorem palm_invariant (S : PalmSetting Ω)
    (hshift : Measurable fun ω => S.θ (S.N.T 1 ω) ω) :
    Measure.map (fun ω => S.θ (S.N.T 1 ω) ω) S.P0 = S.P0 := by sorry

end PalmQueueing.Palm
