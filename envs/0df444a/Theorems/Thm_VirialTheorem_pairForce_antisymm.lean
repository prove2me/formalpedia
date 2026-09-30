-- Prove2me | Theorems.Thm_VirialTheorem_pairForce_antisymm
-- name    : VirialTheorem.pairForce_antisymm
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-28T18:17:17.550228+00:00
-- url     : https://prove2.me/theorems/a1a8c230-ce50-4306-a3f9-b72c2c33f3d2
-- title:
--   Potential pair forces satisfy Newton's third law
-- statement:
--   Let $x_1,\dots,x_N\in\mathbb R^3$ be pairwise distinct and let $V_{jk}:\mathbb R\to\mathbb R$ be pair potentials with $V_{jk}=V_{kj}$, each $V_{jk}$ ($j\ne k$) differentiable at the distance $\|x_k-x_j\|$. Then the forces $F_{jk}=-\nabla_{x_k}V_{jk}(\|x_k-x_j\|)$ (with $F_{kk}=0$) satisfy
--   $$F_{jk}=-F_{kj}\qquad\text{for all } j,k.$$
-- source:
--   Wikipedia, "Virial theorem" (article supplied as Virial_theorem.pdf), https://en.wikipedia.org/wiki/Virial_theorem, section 'Connection with the potential energy between particles' (F_kj = -F_jk)

import Mathlib
import Definitions.Def_virial_theorem_defs

open Filter Topology

namespace VirialTheorem

theorem pairForce_antisymm {N : ℕ} (V : Fin N → Fin N → ℝ → ℝ) (x : Fin N → Space)
    (hsymm : ∀ j k, V j k = V k j)
    (hx : ∀ j k, j ≠ k → x j ≠ x k)
    (hV : ∀ j k, j ≠ k → DifferentiableAt ℝ (V j k) (dist (x k) (x j))) :
    ∀ j k, pairForce V x j k = -pairForce V x k j := by sorry

end VirialTheorem
