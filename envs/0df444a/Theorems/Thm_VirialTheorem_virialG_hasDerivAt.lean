-- Prove2me | Theorems.Thm_VirialTheorem_virialG_hasDerivAt
-- name    : VirialTheorem.virialG_hasDerivAt
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-28T17:32:30.364984+00:00
-- url     : https://prove2.me/theorems/d0e60b1d-135d-49e9-aef6-cc03a702c7ef
-- title:
--   $dG/dt = 2T + \sum_k F_k\cdot r_k$
-- statement:
--   Throughout, $N$ point particles move in $\mathbb R^3$; particle $k$ has constant mass $m_k\in\mathbb R$, position $r_k(t)$ and velocity $v_k(t)$, and momentum $p_k=m_kv_k$. Let $F_k(t)$ be the net force on particle $k$, i.e. $F_k=\frac{dp_k}{dt}$. If at time $t$ each $r_k$ has derivative $v_k(t)$ and each momentum $p_k=m_kv_k$ has derivative $F_k(t)$, then $G=\sum_k p_k\cdot r_k$ is differentiable at $t$ and
--   $$\frac{dG}{dt}(t)=2T(t)+\sum_{k=1}^N F_k(t)\cdot r_k(t),\qquad T=\tfrac12\sum_k m_k\|v_k\|^2 .$$
-- source:
--   Wikipedia, "Virial theorem" (article supplied as Virial_theorem.pdf), https://en.wikipedia.org/wiki/Virial_theorem, section 'Statement and derivation' (derivation of dG/dt)

import Mathlib
import Definitions.Def_virial_theorem_defs

open Filter Topology

namespace VirialTheorem

theorem virialG_hasDerivAt {N : ℕ} (m : Fin N → ℝ) (r v F : Fin N → ℝ → Space) (t : ℝ)
    (hr : ∀ k, HasDerivAt (r k) (v k t) t)
    (hp : ∀ k, HasDerivAt (fun s => m k • v k s) (F k t) t) :
    HasDerivAt (virialG m r v) (2 * kineticEnergy m v t + ∑ k, inner ℝ (F k t) (r k t)) t := by sorry

end VirialTheorem
