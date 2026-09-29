-- Prove2me | Theorems.Thm_SDYM_ramanujan_tau_of_ramanujan_q
-- name    : SDYM.ramanujan_tau_of_ramanujan_q
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T01:52:42.318972+00:00
-- url     : https://prove2.me/theorems/f466b963-f418-41ac-8b4d-a3ba9a2ecfbd
-- title:
--   Ramanujan's system in $\tau$: the change of variable $q = e^{2i\tau}$
-- statement:
--   The passage from equation (78) to equation (79) of the source. Substituting $q = e^{2\pi i t}$ and $\tau = \pi t$, so that $q = e^{2i\tau}$ and $q\,d/dq = \tfrac{1}{2i}\,d/d\tau$, converts Ramanujan's system
--
--   $$q\frac{dP}{dq} = \frac{P^2-Q}{12},\qquad q\frac{dQ}{dq} = \frac{PQ-R}{3},\qquad q\frac{dR}{dq} = \frac{PR-Q^2}{2}$$
--
--   into the system in the additive variable
--
--   $$\frac{dP}{d\tau} = \frac{i}{6}(P^2-Q),\qquad \frac{dQ}{d\tau} = \frac{2i}{3}(PQ-R),\qquad \frac{dR}{d\tau} = i(PR-Q^2).$$
--
--   This is the step that removes the singular factor $q$ and makes the elimination of $Q$ and $R$ a constant-coefficient computation. It is also where the domain changes: the system in $\tau$ holds on the preimage of the original domain under $\tau \mapsto e^{2i\tau}$.
--
--   **Conventions shared with the rest of the mission.** All functions are complex-valued functions of a complex variable; a system is required to hold only at the points of an arbitrary set $s \subseteq \mathbb{C}$, with no openness, connectedness or holomorphy assumed; and each derivative that a statement mentions is carried by an explicit companion function tied to it by a pointwise differentiability assertion, so no statement ever refers to the value of a derivative that does not exist.
-- source:
--   M. J. Ablowitz, S. Chakravarty, R. G. Halburd, "Integrable systems and reductions of the self-dual Yang-Mills equations", J. Math. Phys. 44 (2003) 3147-3173, https://doi.org/10.1063/1.1586967, Sec. V.A p. 3170, the sentence "Using q = e^{2πit}, τ = πt, the equations (78) take the form (79)"

import Definitions.Def_SDYM_ChazyEquations
import Definitions.Def_SDYM_DarbouxHalphenRamanujan

namespace SDYM

theorem ramanujan_tau_of_ramanujan_q
    (U : Set ℂ) (P Q R Pd Qd Rd : ℂ → ℂ)
    (h : IsRamanujanQSolution U P Q R Pd Qd Rd) :
    IsRamanujanTauSolution {z : ℂ | Complex.exp (2 * Complex.I * z) ∈ U}
      (fun z => P (Complex.exp (2 * Complex.I * z)))
      (fun z => Q (Complex.exp (2 * Complex.I * z)))
      (fun z => R (Complex.exp (2 * Complex.I * z))) := by sorry

end SDYM
