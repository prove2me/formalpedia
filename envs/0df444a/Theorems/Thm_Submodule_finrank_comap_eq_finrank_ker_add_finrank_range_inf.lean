-- Prove2me | Theorems.Thm_Submodule_finrank_comap_eq_finrank_ker_add_finrank_range_inf
-- name    : Submodule.finrank_comap_eq_finrank_ker_add_finrank_range_inf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/198724cd-91da-5afa-adec-8640b957cb4a
-- title:
--   Dimension of a preimage subspace: rank–nullity for `comap`
-- statement:
--   Let $k$ be a field and let $V$ and $W$ be additive commutative groups equipped with $k$-module structures. Given a $k$-linear map $f : V \to W$ and a $k$-submodule $N \subseteq W$, and assuming that the preimage $f^{-1}(N)$ — the submodule `N.comap f` of $V$ — is finite-dimensional over $k$, the assertion is the equality of natural numbers
--   $$\operatorname{finrank}_k f^{-1}(N) \;=\; \operatorname{finrank}_k \ker f \;+\; \operatorname{finrank}_k\bigl(\operatorname{range} f \sqcap N\bigr),$$
--   where the last term is the $k$-dimension of the submodule $\operatorname{im} f \cap N$ of $W$. Note that no finiteness hypothesis is imposed on $V$, on $W$ or on $N$ itself: only the preimage is assumed finite-dimensional, which already forces $\ker f$ and $\operatorname{im} f \cap N$ to be finite-dimensional, so that all three ranks are genuine dimensions and the equation is not an artefact of the convention that `finrank` vanishes on infinite-dimensional spaces.
--
--   This is rank–nullity applied to the restriction of $f$ to the preimage $f^{-1}(N)$, whose kernel is $\ker f$ and whose image is $\operatorname{im} f \cap N$. It is used in the Greenberg–Wiles/Poitou–Tate dimension count, where a Selmer group is realised as the preimage under the localisation map of a product of local conditions, and is cited by [`groupCohomology.greenbergWilesLeAdm_extArithLoc_of_isTheta1_eval_of_ne_two`](thm.html#groupCohomology.greenbergWilesLeAdm_extArithLoc_of_isTheta1_eval_of_ne_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Submodule_finrank_comap_eq_finrank_ker_add_finrank_range_inf.lean

import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.OrderOfElement

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Module

theorem Submodule.finrank_comap_eq_finrank_ker_add_finrank_range_inf
    {k : Type*} [Field k] {V W : Type*} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (f : V →ₗ[k] W) (N : Submodule k W) [FiniteDimensional k (N.comap f)] :
    finrank k (N.comap f)
      = finrank k (LinearMap.ker f) + finrank k (LinearMap.range f ⊓ N : Submodule k W) := by sorry
