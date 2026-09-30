-- Prove2me | Theorems.Thm_VirialTheorem_virialG_hasDerivAt_power_law
-- name    : VirialTheorem.virialG_hasDerivAt_power_law
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-28T18:56:27.540612+00:00
-- url     : https://prove2.me/theorems/d2eee8ae-d407-4d87-983f-13407e25e832
-- title:
--   Power-law forces: $dG/dt = 2T - n\,V_{\mathrm{TOT}}$
-- statement:
--   Throughout, $N$ point particles move in $\mathbb R^3$; particle $k$ has constant mass $m_k\in\mathbb R$, position $r_k(t)$ and velocity $v_k(t)$, and momentum $p_k=m_kv_k$. Suppose the only forces are power-law pair forces, $V_{jk}(s)=\alpha_{jk}s^n$ with $\alpha_{jk}=\alpha_{kj}$, so that at time $t$ each momentum $p_k$ has derivative $F_k(t)=\sum_jF_{jk}(r(t))$. If moreover $r_k$ has derivative $v_k(t)$ at $t$ and the particles occupy pairwise distinct positions at time $t$, then
--   $$\frac{dG}{dt}(t)=2T(t)-n\,V_{\mathrm{TOT}}(t).$$
-- source:
--   Wikipedia, "Virial theorem" (article supplied as Virial_theorem.pdf), https://en.wikipedia.org/wiki/Virial_theorem, section 'Special case of power-law forces' (dG/dt = 2T - nV_TOT)

import Mathlib
import Definitions.Def_virial_theorem_defs

open Filter Topology

namespace VirialTheorem

theorem virialG_hasDerivAt_power_law {N : ℕ} (m : Fin N → ℝ) (r v : Fin N → ℝ → Space)
    (α : Fin N → Fin N → ℝ) (n : ℝ) (t : ℝ)
    (hα : ∀ j k, α j k = α k j)
    (hr : ∀ k, HasDerivAt (r k) (v k t) t)
    (hp : ∀ k, HasDerivAt (fun s => m k • v k s)
      (netPairForce (powerLawPotential α n) (fun i => r i t) k) t)
    (hx : ∀ j k, j ≠ k → r j t ≠ r k t) :
    HasDerivAt (virialG m r v)
      (2 * kineticEnergy m v t - n * totalPotential (powerLawPotential α n) (fun i => r i t)) t := by sorry

end VirialTheorem
