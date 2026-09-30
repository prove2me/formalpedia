-- Prove2me | Theorems.Thm_VirialTheorem_timeAverage_virialG_deriv
-- name    : VirialTheorem.timeAverage_virialG_deriv
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-28T19:03:24.763228+00:00
-- url     : https://prove2.me/theorems/6ecde9db-059d-4c8e-a11a-e4983e1c3a62
-- title:
--   Exact time-averaged equation $\langle dG/dt\rangle_\tau = 2\langle T\rangle_\tau+\sum_k\langle F_k\cdot r_k\rangle_\tau$
-- statement:
--   Throughout, $N$ point particles move in $\mathbb R^3$; particle $k$ has constant mass $m_k\in\mathbb R$, position $r_k(t)$ and velocity $v_k(t)$, and momentum $p_k=m_kv_k$. Suppose for all times $t$ that $\dot r_k=v_k$ and $\dot p_k=F_k$, with each force $F_k$ continuous in time. Then for every duration $\tau>0$,
--   $$\left\langle\frac{dG}{dt}\right\rangle_\tau=\frac{G(\tau)-G(0)}{\tau}\qquad\text{and}\qquad\left\langle\frac{dG}{dt}\right\rangle_\tau=2\langle T\rangle_\tau+\sum_{k=1}^N\langle F_k\cdot r_k\rangle_\tau,$$
--   where $\langle f\rangle_\tau=\frac1\tau\int_0^\tau f\,dt$.
--
--   **Formalization Note** Continuity of the forces is the standing smoothness convention of classical mechanics; it makes all the averaged quantities integrable.
-- source:
--   Wikipedia, "Virial theorem" (article supplied as Virial_theorem.pdf), https://en.wikipedia.org/wiki/Virial_theorem, section 'Time averaging' (exact equation)

import Mathlib
import Definitions.Def_virial_theorem_defs

open Filter Topology

namespace VirialTheorem

theorem timeAverage_virialG_deriv {N : ℕ} (m : Fin N → ℝ) (r v F : Fin N → ℝ → Space)
    (hr : ∀ k t, HasDerivAt (r k) (v k t) t)
    (hp : ∀ k t, HasDerivAt (fun s => m k • v k s) (F k t) t)
    (hF : ∀ k, Continuous (F k))
    (τ : ℝ) (hτ : 0 < τ) :
    timeAverage (deriv (virialG m r v)) τ = (virialG m r v τ - virialG m r v 0) / τ ∧
    timeAverage (deriv (virialG m r v)) τ =
      2 * timeAverage (kineticEnergy m v) τ +
        ∑ k, timeAverage (fun t => inner ℝ (F k t) (r k t)) τ := by sorry

end VirialTheorem
