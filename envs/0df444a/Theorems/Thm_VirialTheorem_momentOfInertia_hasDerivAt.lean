-- Prove2me | Theorems.Thm_VirialTheorem_momentOfInertia_hasDerivAt
-- name    : VirialTheorem.momentOfInertia_hasDerivAt
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-28T17:08:55.2351+00:00
-- url     : https://prove2.me/theorems/962345c6-809e-4e86-becc-34c4f3e2f888
-- title:
--   Half the derivative of the moment of inertia is $G$
-- statement:
--   Throughout, $N$ point particles move in $\mathbb R^3$; particle $k$ has constant mass $m_k\in\mathbb R$, position $r_k(t)$ and velocity $v_k(t)$, and momentum $p_k=m_kv_k$. Let $I(t)=\sum_k m_k\|r_k(t)\|^2$ and $G(t)=\sum_k p_k(t)\cdot r_k(t)$. If at time $t$ every $r_k$ is differentiable with derivative $v_k(t)$, then $I$ is differentiable at $t$ and
--   $$\frac{dI}{dt}(t)=2\,G(t).$$
--
--   This identifies $G$ as half the rate of change of the moment of inertia, the first step of the derivation of the virial theorem.
-- source:
--   Wikipedia, "Virial theorem" (article supplied as Virial_theorem.pdf), https://en.wikipedia.org/wiki/Virial_theorem, section 'Statement and derivation' (derivation of dI/dt)

import Mathlib
import Definitions.Def_virial_theorem_defs

open Filter Topology

namespace VirialTheorem

theorem momentOfInertia_hasDerivAt {N : ℕ} (m : Fin N → ℝ) (r v : Fin N → ℝ → Space) (t : ℝ)
    (hr : ∀ k, HasDerivAt (r k) (v k t) t) :
    HasDerivAt (momentOfInertia m r) (2 * virialG m r v t) t := by sorry

end VirialTheorem
