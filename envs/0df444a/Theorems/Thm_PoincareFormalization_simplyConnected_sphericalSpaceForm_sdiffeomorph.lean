-- Prove2me | Theorems.Thm_PoincareFormalization_simplyConnected_sphericalSpaceForm_sdiffeomorph
-- name    : PoincareFormalization.simplyConnected_sphericalSpaceForm_sdiffeomorph
-- status  : Open
-- author  : @wojtek_politarczyk
-- created : 2026-11-24T20:41:19.943662+00:00
-- url     : https://prove2.me/theorems/f0aabe6c-8754-46e3-95d8-25cff06b8675
-- title:
--   A simply connected spherical $3$-space form is diffeomorphic to $\mathbb{S}^3$
-- statement:
--   Let $M$ be a closed, connected, simply connected smooth $3$-manifold that is a spherical space form, meaning it admits a finite-sheeted smooth covering map $p : \mathbb{S}^3 \to M$ that is locally a diffeomorphism. Then $M$ is diffeomorphic to $\mathbb{S}^3$:
--
--   $$M \simeq_{\mathrm{diff}} \mathbb{S}^3.$$
--
--   Since $M$ is simply connected and locally path-connected and $\mathbb{S}^3$ is connected, any covering map $p : \mathbb{S}^3 \to M$ is a bijection; local smooth invertibility then promotes $p^{-1}$ to a diffeomorphism.
--
--   **Formalization Note** Spherical space forms are formalized by `IsSphericalSpaceForm M`.
-- source:
--   A. Hatcher, Algebraic Topology (2002), Proposition 1.31–1.32 (covering spaces of simply connected spaces), pp. 61–62.

import Definitions.Def_PoincareFormalization_SmoothSurgery
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

set_option autoImplicit false

open scoped Manifold ContDiff

namespace PoincareFormalization

theorem simplyConnected_sphericalSpaceForm_sdiffeomorph
    (M : SmoothThreeManifold) (h : IsSphericalSpaceForm M)
    [SimplyConnectedSpace M.Carrier] :
    Nonempty (M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ S3) := by
  sorry

end PoincareFormalization
