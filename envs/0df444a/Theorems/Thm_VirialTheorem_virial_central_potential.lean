-- Prove2me | Theorems.Thm_VirialTheorem_virial_central_potential
-- name    : VirialTheorem.virial_central_potential
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-28T18:25:22.158182+00:00
-- url     : https://prove2.me/theorems/d913f272-e489-46ea-9413-a2aadd02b40c
-- title:
--   Virial of potential pair forces: $\sum_k F_k\cdot r_k=-\sum_{j<k}V'_{jk}(r_{jk})\,r_{jk}$
-- statement:
--   Let $x_1,\dots,x_N\in\mathbb R^3$ be pairwise distinct and let $V_{jk}:\mathbb R\to\mathbb R$ be pair potentials with $V_{jk}=V_{kj}$, each $V_{jk}$ ($j\ne k$) differentiable at $r_{jk}=\|x_k-x_j\|$. With $F_{jk}=-\nabla_{x_k}V_{jk}(\|x_k-x_j\|)$ and $F_k=\sum_j F_{jk}$,
--   $$\sum_{k=1}^N F_k\cdot x_k=-\sum_{k=1}^N\sum_{j<k}V_{jk}'(r_{jk})\,r_{jk}.$$
-- source:
--   Wikipedia, "Virial theorem" (article supplied as Virial_theorem.pdf), https://en.wikipedia.org/wiki/Virial_theorem, section 'Connection with the potential energy between particles' (final formula)

import Mathlib
import Definitions.Def_virial_theorem_defs

open Filter Topology

namespace VirialTheorem

theorem virial_central_potential {N : ℕ} (V : Fin N → Fin N → ℝ → ℝ) (x : Fin N → Space)
    (hsymm : ∀ j k, V j k = V k j)
    (hx : ∀ j k, j ≠ k → x j ≠ x k)
    (hV : ∀ j k, j ≠ k → DifferentiableAt ℝ (V j k) (dist (x k) (x j))) :
    ∑ k, inner ℝ (netPairForce V x k) (x k) =
      -∑ k, ∑ j ∈ Finset.univ.filter (fun j => j < k),
        deriv (V j k) (dist (x k) (x j)) * dist (x k) (x j) := by sorry

end VirialTheorem
