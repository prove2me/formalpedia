-- Prove2me | Theorems.Thm_VirialTheorem_virial_sum_pairs
-- name    : VirialTheorem.virial_sum_pairs
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-28T17:43:41.8047+00:00
-- url     : https://prove2.me/theorems/95fc5e9a-7ea1-4667-96c9-2b5b31011c47
-- title:
--   Virial as a sum over pairs (Newton's third law)
-- statement:
--   Let $x_1,\dots,x_N\in\mathbb R^3$ be positions and $F_{jk}\in\mathbb R^3$ ($1\le j,k\le N$) be the force of particle $j$ on particle $k$, satisfying Newton's third law $F_{jk}=-F_{kj}$ for all $j,k$ (in particular $F_{jj}=0$). With $F_k=\sum_j F_{jk}$,
--   $$\sum_{k=1}^N F_k\cdot x_k=\sum_{k=1}^N\sum_{j<k}F_{jk}\cdot(x_k-x_j).$$
--
--   This rewrites the virial as a sum over unordered pairs.
-- source:
--   Wikipedia, "Virial theorem" (article supplied as Virial_theorem.pdf), https://en.wikipedia.org/wiki/Virial_theorem, section 'Connection with the potential energy between particles' (pair splitting)

import Mathlib
import Definitions.Def_virial_theorem_defs

open Filter Topology

namespace VirialTheorem

theorem virial_sum_pairs {N : ℕ} (Fp : Fin N → Fin N → Space) (x : Fin N → Space)
    (hanti : ∀ j k, Fp j k = -Fp k j) :
    ∑ k, inner ℝ (∑ j, Fp j k) (x k) =
      ∑ k, ∑ j ∈ Finset.univ.filter (fun j => j < k), inner ℝ (Fp j k) (x k - x j) := by sorry

end VirialTheorem
