-- Prove2me | Theorems.Thm_VirialTheorem_virial_theorem
-- name    : VirialTheorem.virial_theorem
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-28T19:25:35.758978+00:00
-- url     : https://prove2.me/theorems/3ae91b60-f3cd-4519-a939-1fc33b525ae8
-- title:
--   Virial theorem: $2\langle T\rangle_\tau+\sum_k\langle F_k\cdot r_k\rangle_\tau\to0$ for bounded motion
-- statement:
--   Throughout, $N$ point particles move in $\mathbb R^3$; particle $k$ has constant mass $m_k\in\mathbb R$, position $r_k(t)$ and velocity $v_k(t)$, and momentum $p_k=m_kv_k$. Let $F_k(t)$ be the net force on particle $k$, so that $\dot r_k=v_k$ and $\dot p_k=F_k$ for all $t$, with each $F_k$ continuous. Suppose the motion is bounded: there is a constant $C$ with $\|r_k(t)\|\le C$ and $\|v_k(t)\|\le C$ for all $k$ and all $t\ge0$. Then, with $T=\frac12\sum_km_k\|v_k\|^2$ and $\langle f\rangle_\tau=\frac1\tau\int_0^\tau f\,dt$,
--   $$\lim_{\tau\to\infty}\Big(2\langle T\rangle_\tau+\sum_{k=1}^N\langle F_k\cdot r_k\rangle_\tau\Big)=0,$$
--   i.e. in the long-time limit $\langle T\rangle=-\frac12\sum_k\langle F_k\cdot r_k\rangle$.
--
--   This is the virial theorem of classical mechanics, relating the time-averaged kinetic energy of a stably bound system to the time-averaged virial of the forces.
--
--   **Formalization Note** The theorem is stated as a limit of the difference, since for a bounded motion the individual averages need not converge. Continuity of the forces is the standing smoothness convention.
-- source:
--   Wikipedia, "Virial theorem" (article supplied as Virial_theorem.pdf), https://en.wikipedia.org/wiki/Virial_theorem, introduction and section 'Time averaging' (virial theorem)

import Mathlib
import Definitions.Def_virial_theorem_defs

open Filter Topology

namespace VirialTheorem

theorem virial_theorem {N : ℕ} (m : Fin N → ℝ) (r v F : Fin N → ℝ → Space)
    (hr : ∀ k t, HasDerivAt (r k) (v k t) t)
    (hp : ∀ k t, HasDerivAt (fun s => m k • v k s) (F k t) t)
    (hF : ∀ k, Continuous (F k))
    (hbdd : ∃ C : ℝ, ∀ t ≥ 0, ∀ k, ‖r k t‖ ≤ C ∧ ‖v k t‖ ≤ C) :
    Tendsto (fun τ => 2 * timeAverage (kineticEnergy m v) τ +
        ∑ k, timeAverage (fun t => inner ℝ (F k t) (r k t)) τ) atTop (𝓝 0) := by sorry

end VirialTheorem
