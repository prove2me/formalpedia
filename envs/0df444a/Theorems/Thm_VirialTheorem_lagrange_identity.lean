-- Prove2me | Theorems.Thm_VirialTheorem_lagrange_identity
-- name    : VirialTheorem.lagrange_identity
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-28T18:59:36.618978+00:00
-- url     : https://prove2.me/theorems/b09cf087-2633-4cc5-903c-ee0234cb37c5
-- title:
--   Lagrange's identity: $\tfrac12 \ddot I = 2T + V_{\mathrm{TOT}}$ for $n=-1$
-- statement:
--   Throughout, $N$ point particles move in $\mathbb R^3$; particle $k$ has constant mass $m_k\in\mathbb R$, position $r_k(t)$ and velocity $v_k(t)$, and momentum $p_k=m_kv_k$. Suppose each $r_k$ is differentiable at all times with derivative $v_k$, the particles are pairwise distinct at time $t$, and at time $t$ each momentum has derivative equal to the net force from inverse-distance pair potentials $V_{jk}(s)=\alpha_{jk}s^{-1}$ with $\alpha_{jk}=\alpha_{kj}$. Then
--   $$\frac12\frac{d^2I}{dt^2}(t)=2T(t)+V_{\mathrm{TOT}}(t).$$
-- source:
--   Wikipedia, "Virial theorem" (article supplied as Virial_theorem.pdf), https://en.wikipedia.org/wiki/Virial_theorem, section 'Special case of power-law forces' (Lagrange's identity)

import Mathlib
import Definitions.Def_virial_theorem_defs

open Filter Topology

namespace VirialTheorem

theorem lagrange_identity {N : ℕ} (m : Fin N → ℝ) (r v : Fin N → ℝ → Space)
    (α : Fin N → Fin N → ℝ) (t : ℝ)
    (hα : ∀ j k, α j k = α k j)
    (hr : ∀ k s, HasDerivAt (r k) (v k s) s)
    (hp : ∀ k, HasDerivAt (fun s => m k • v k s)
      (netPairForce (powerLawPotential α (-1)) (fun i => r i t) k) t)
    (hx : ∀ j k, j ≠ k → r j t ≠ r k t) :
    (1 / 2 : ℝ) * deriv (deriv (momentOfInertia m r)) t =
      2 * kineticEnergy m v t + totalPotential (powerLawPotential α (-1)) (fun i => r i t) := by sorry

end VirialTheorem
