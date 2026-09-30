-- Prove2me | Theorems.Thm_VirialTheorem_timeAverage_virialG_deriv_tendsto_zero
-- name    : VirialTheorem.timeAverage_virialG_deriv_tendsto_zero
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-28T19:13:46.310841+00:00
-- url     : https://prove2.me/theorems/39957aee-5153-4bc2-95d8-23e39e0a2a3b
-- title:
--   Bounded motion: $\langle dG/dt\rangle_\tau\to0$
-- statement:
--   Throughout, $N$ point particles move in $\mathbb R^3$; particle $k$ has constant mass $m_k\in\mathbb R$, position $r_k(t)$ and velocity $v_k(t)$, and momentum $p_k=m_kv_k$. Suppose for all times that $\dot r_k=v_k$ and $\dot p_k=F_k$ with continuous forces, and that the motion is bounded: there is a constant $C$ with $\|r_k(t)\|\le C$ and $\|v_k(t)\|\le C$ for all $k$ and all $t\ge0$. Then
--   $$\lim_{\tau\to\infty}\left\langle\frac{dG}{dt}\right\rangle_\tau=0 .$$
-- source:
--   Wikipedia, "Virial theorem" (article supplied as Virial_theorem.pdf), https://en.wikipedia.org/wiki/Virial_theorem, section 'Time averaging' (stably bound systems)

import Mathlib
import Definitions.Def_virial_theorem_defs

open Filter Topology

namespace VirialTheorem

theorem timeAverage_virialG_deriv_tendsto_zero {N : ℕ} (m : Fin N → ℝ)
    (r v F : Fin N → ℝ → Space)
    (hr : ∀ k t, HasDerivAt (r k) (v k t) t)
    (hp : ∀ k t, HasDerivAt (fun s => m k • v k s) (F k t) t)
    (hF : ∀ k, Continuous (F k))
    (hbdd : ∃ C : ℝ, ∀ t ≥ 0, ∀ k, ‖r k t‖ ≤ C ∧ ‖v k t‖ ≤ C) :
    Tendsto (fun τ => timeAverage (deriv (virialG m r v)) τ) atTop (𝓝 0) := by sorry

end VirialTheorem
