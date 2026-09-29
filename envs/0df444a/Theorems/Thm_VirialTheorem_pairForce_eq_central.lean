-- Prove2me | Theorems.Thm_VirialTheorem_pairForce_eq_central
-- name    : VirialTheorem.pairForce_eq_central
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-28T17:48:33.046471+00:00
-- url     : https://prove2.me/theorems/8c093b36-a4ee-4551-a70e-14b406f68acd
-- title:
--   Potential pair forces are central
-- statement:
--   Let $x_1,\dots,x_N\in\mathbb R^3$ and let $V_{jk}:\mathbb R\to\mathbb R$ be pair potentials. Fix $j\ne k$ with $x_j\ne x_k$, put $r_{jk}=\|x_k-x_j\|>0$, and assume $V_{jk}$ is differentiable at $r_{jk}$. Then the force $F_{jk}=-\nabla_{x_k}V_{jk}(\|x_k-x_j\|)$ equals
--   $$F_{jk}=-\frac{V_{jk}'(r_{jk})}{r_{jk}}\,(x_k-x_j).$$
-- source:
--   Wikipedia, "Virial theorem" (article supplied as Virial_theorem.pdf), https://en.wikipedia.org/wiki/Virial_theorem, section 'Connection with the potential energy between particles' (F_jk = -grad V_jk)

import Mathlib
import Definitions.Def_virial_theorem_defs

open Filter Topology

namespace VirialTheorem

theorem pairForce_eq_central {N : ℕ} (V : Fin N → Fin N → ℝ → ℝ) (x : Fin N → Space)
    (j k : Fin N) (hjk : j ≠ k) (hx : x j ≠ x k)
    (hV : DifferentiableAt ℝ (V j k) (dist (x k) (x j))) :
    pairForce V x j k =
      -(deriv (V j k) (dist (x k) (x j)) / dist (x k) (x j)) • (x k - x j) := by sorry

end VirialTheorem
