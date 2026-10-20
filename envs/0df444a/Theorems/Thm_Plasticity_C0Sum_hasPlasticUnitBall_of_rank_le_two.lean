-- Prove2me | Theorems.Thm_Plasticity_C0Sum_hasPlasticUnitBall_of_rank_le_two
-- name    : Plasticity.C0Sum.hasPlasticUnitBall_of_rank_le_two
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-19T18:59:53.231792+00:00
-- url     : https://prove2.me/theorems/386ac7e6-5b85-4c18-857d-be711da2cfd8
-- title:
--   Every $c_0$ sum of real spaces of dimension at most two has a plastic unit ball
-- statement:
--   Let $(E_i)_{i\in I}$ be a family of real normed spaces over an arbitrary index set, with every $E_i$ of dimension at most two (zero allowed).
--   The closed unit ball of the $c_0$ sum $c_0(I;E_i)$ with the supremum block norm is plastic: every nonexpansive bijection of it onto itself is an isometry.
--   In particular the ball of every $c_0$ sum of real planes is plastic, whatever the planes.
--
--   **Formalization Note** "Dimension at most two" is `Module.rank ℝ (E i) ≤ 2`.
-- source:
--   This repository: claim CUB109 (claims/cub.md), proof in expositions/c0_planes_with_scalars.md §4

import Definitions.Def_Plasticity_Basic
import Definitions.Def_Plasticity_C0Sum
import Mathlib.LinearAlgebra.Dimension.Finrank

namespace Plasticity.C0Sum
theorem hasPlasticUnitBall_of_rank_le_two {ι : Type*}
    (E : ι → Type*) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    (hE : ∀ i, Module.rank ℝ (E i) ≤ 2) : HasPlasticUnitBall (c0Sum E) := by sorry
end Plasticity.C0Sum
